"""코스피·코스닥 아침 스크리너.

매 거래일 아침 실행하면 직전 거래일까지의 일봉으로 여러 조건(항목)을 계산해
results/latest.json 과 results/history.json 에 저장한다.

항목을 늘리려면: 아래 SCREENS 에 {id, name, fn} 하나를 추가하면 된다.
fn(bars, i) 는 i번째 거래일이 조건에 맞으면 표에 보일 값(dict)을, 아니면 None 을 돌려준다.

데이터: 네이버 금융 일봉 (실패 시 pykrx 로 대체)
"""
from __future__ import annotations

import json
import math
import os
import re
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone

import requests

MARKETS = ("KOSPI", "KOSDAQ")
BARS = 300          # 받아올 일봉 개수 (52주 = 250거래일 + 여유)
HISTORY_DAYS = 20    # history.json 에 남길 최근 거래일 수
KST = timezone(timedelta(hours=9))
UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                    "(KHTML, like Gecko) Chrome/126.0 Safari/537.36"}
OUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")


# ================================================================ 공통 값
def common(bars, i):
    c, pc = bars[i]["close"], bars[i - 1]["close"]
    v = bars[i]["volume"]
    prev20 = [b["volume"] for b in bars[max(0, i - 20):i]]
    avg20 = sum(prev20) / len(prev20) if prev20 else 0
    return {
        "close": c,
        "changePct": round((c / pc - 1) * 100, 2) if pc else None,
        "volume": v,
        "volRatio": round(v / avg20, 2) if avg20 else None,
        "tradeValue": int(c * v),
    }


# ================================================================ 항목 1: 52주 신고가
WEEKS52 = 364  # 52주 = 364일 (달력 기준)


def high52(bars, i):
    """당일 고가가 직전 52주(기준일 364일 전 ~ 전일) 최고가를 넘어선 종목.
    상장(또는 데이터 시작)이 52주가 안 된 종목은 비교할 수 없어 제외."""
    if i < 1 or bars[i]["volume"] <= 0:
        return None
    d = datetime.strptime(bars[i]["date"], "%Y-%m-%d").date()
    cutoff = (d - timedelta(days=WEEKS52)).isoformat()
    if bars[0]["date"] > cutoff:
        return None
    window = [b for b in bars[:i] if b["date"] >= cutoff]
    highs = [b["high"] for b in window]
    prior = max(highs)
    h = bars[i]["high"]
    if prior <= 0 or h <= prior:
        return None
    # 직전 고점이 찍힌 뒤 몇 거래일 만의 경신인지 (길수록 오래 눌려 있던 고점을 뚫은 것)
    last_idx = max(j for j, x in enumerate(highs) if x == prior)
    gap = len(window) - last_idx
    closes = [b["close"] for b in window]
    row = common(bars, i)
    row.update({
        "high": h,
        "prevHigh": prior,
        "breakPct": round((h / prior - 1) * 100, 2),
        "closeNewHigh": bars[i]["close"] > max(closes),   # 종가로도 52주 최고인지
        "daysSincePrevHigh": gap,
        "closeToHighPct": round((bars[i]["close"] / h - 1) * 100, 2),  # 고가 대비 종가 (윗꼬리)
    })
    return row


# ================================================================ 항목 2: 볼린저밴드 상단 돌파
BB_N, BB_K = 20, 2.0


def _band(closes, end):
    """closes[end-BB_N+1 .. end] 의 (중심, 상단, 하단). 모집단 표준편차."""
    win = closes[end + 1 - BB_N:end + 1]
    m = sum(win) / BB_N
    sd = math.sqrt(sum((x - m) ** 2 for x in win) / BB_N)
    return m, m + BB_K * sd, m - BB_K * sd


def bb_upper(bars, i):
    """전일 종가 ≤ 전일 상단 이고 당일 종가 > 당일 상단."""
    if i < BB_N or bars[i]["volume"] <= 0:
        return None
    closes = [b["close"] for b in bars[:i + 1]]
    mid, up, lo = _band(closes, i)
    _, pup, _ = _band(closes, i - 1)
    if not (closes[i] > up and closes[i - 1] <= pup):
        return None
    row = common(bars, i)
    row.update({
        "upper": round(up, 1),
        "middle": round(mid, 1),
        "abovePct": round((closes[i] / up - 1) * 100, 2),
        "bandWidthPct": round((up - lo) / mid * 100, 2) if mid else None,
    })
    return row


SCREENS = [
    {"id": "high52", "name": "52주 신고가", "fn": high52,
     "rule": "당일 고가 > 직전 52주(364일) 최고가"},
    {"id": "bb_upper", "name": "볼린저밴드 상단 돌파", "fn": bb_upper,
     "rule": "20일·2σ, 전일 종가 ≤ 상단 → 당일 종가 > 상단"},
]


# ================================================================ 네이버
def naver_universe() -> list[dict]:
    items, page = [], 1
    for market in MARKETS:
        page = 1
        while True:
            r = requests.get(f"https://m.stock.naver.com/api/stocks/marketValue/{market}",
                             params={"page": page, "pageSize": 100}, headers=UA, timeout=20)
            r.raise_for_status()
            js = r.json()
            stocks = js.get("stocks", [])
            for s in stocks:
                if str(s.get("stockEndType", "")).lower() in ("etf", "etn"):
                    continue
                items.append({"code": s["itemCode"], "name": s["stockName"], "market": market})
            if not stocks or page * 100 >= js.get("totalCount", 0):
                break
            page += 1
            time.sleep(0.2)
        n = sum(1 for x in items if x["market"] == market)
        if n < 300:
            raise RuntimeError(f"{market} 종목 목록이 너무 적음: {n}")
    return items


ITEM_RE = re.compile(r'data="(\d{8})\|([\d.]+)\|([\d.]+)\|([\d.]+)\|([\d.]+)\|(\d+)"')


def naver_bars(code: str) -> list[dict]:
    r = requests.get("https://fchart.stock.naver.com/sise.nhn",
                     params={"symbol": code, "timeframe": "day", "count": BARS, "requestType": 0},
                     headers=UA, timeout=20)
    r.raise_for_status()
    return [{"date": f"{d[:4]}-{d[4:6]}-{d[6:]}", "open": float(o), "high": float(h),
             "low": float(l), "close": float(c), "volume": int(v)}
            for d, o, h, l, c, v in ITEM_RE.findall(r.text)]


def via_naver():
    uni = naver_universe()
    out, fails = {}, 0

    def job(s):
        for attempt in range(3):
            try:
                return s, naver_bars(s["code"])
            except Exception:
                time.sleep(1 + attempt)
        return s, None

    with ThreadPoolExecutor(max_workers=10) as ex:
        for fut in as_completed([ex.submit(job, s) for s in uni]):
            s, bars = fut.result()
            if bars:
                out[s["code"]] = (s, bars)
            else:
                fails += 1
    if len(out) < len(uni) * 0.8:
        raise RuntimeError(f"시세 수집 실패가 많음: 성공 {len(out)} / {len(uni)}")
    return out, "naver", fails


# ================================================================ pykrx (대체)
def via_pykrx():
    from pykrx import stock
    today = datetime.now(KST).date()
    d = today - timedelta(days=1)
    frames = []
    while len(frames) < BARS - 10 and (today - d).days < 460:
        ds = d.strftime("%Y%m%d")
        dfs = {m: stock.get_market_ohlcv(ds, market=m) for m in MARKETS}
        if all(df is not None and len(df) and df["종가"].sum() > 0 for df in dfs.values()):
            frames.append((d.isoformat(), dfs))
        d -= timedelta(days=1)
        time.sleep(0.2)
    frames.reverse()
    if len(frames) < 240:
        raise RuntimeError("pykrx 로 충분한 거래일을 받지 못함")
    all_bars, market_of = {}, {}
    for date, dfs in frames:
        for m, df in dfs.items():
            for code, row in df.iterrows():
                market_of[code] = m
                all_bars.setdefault(code, []).append({
                    "date": date, "open": float(row["시가"]), "high": float(row["고가"]),
                    "low": float(row["저가"]), "close": float(row["종가"]), "volume": int(row["거래량"])})
    out = {code: ({"code": code, "name": stock.get_market_ticker_name(code), "market": market_of[code]}, bars)
           for code, bars in all_bars.items()}
    return out, "pykrx", 0


# ================================================================ 실행
def clean_bar(b):
    """거래정지일 등 시가·고가·저가가 0으로 오는 봉은 종가로 채운다."""
    c = b["close"]
    o, h, l = (x if x > 0 else c for x in (b["open"], b["high"], b["low"]))
    return {**b, "open": o, "high": max(h, c), "low": min(l, c) if l > 0 else c}


def run(all_bars, source, fails):
    n = len(all_bars)
    now_kst = datetime.now(KST)
    # 장 마감(15:30) 뒤 16시 이후에 돌리면 오늘 봉까지 포함, 그 전이면 오늘 봉(장중 미완성)은 제외
    if now_kst.hour >= 16:
        today_kst = (now_kst.date() + timedelta(days=1)).isoformat()
    else:
        today_kst = now_kst.date().isoformat()
    cnt = Counter(b["date"] for _, bars in all_bars.values() for b in bars)
    trading_days = sorted(d for d, c in cnt.items() if c >= n * 0.5 and d < today_kst)
    recent = trading_days[-HISTORY_DAYS:]
    recent_set = set(recent)

    hits = {s["id"]: {d: [] for d in recent} for s in SCREENS}
    universe = {d: {m: 0 for m in MARKETS} for d in recent}
    for code, (meta, bars) in all_bars.items():
        mkt = meta.get("market", "KOSPI")
        bars = sorted((clean_bar(b) for b in bars if b["date"] < today_kst and b["close"] > 0),
                      key=lambda b: b["date"])
        for i, b in enumerate(bars):
            if b["date"] not in recent_set or i == 0:
                continue
            universe[b["date"]][mkt] = universe[b["date"]].get(mkt, 0) + 1
            for s in SCREENS:
                row = s["fn"](bars, i)
                if row:
                    hits[s["id"]][b["date"]].append({"code": code, "name": meta["name"], "market": mkt, **row})

    now = datetime.now(KST).isoformat(timespec="seconds")
    screens_out = {}
    for s in SCREENS:
        days = []
        for d in recent:
            items = sorted(hits[s["id"]][d], key=lambda r: r["tradeValue"], reverse=True)
            days.append({"date": d, "count": len(items), "universe": sum(universe[d].values()),
                         "universeByMarket": universe[d],
                         "countByMarket": {m: sum(1 for r in items if r["market"] == m) for m in MARKETS},
                         "items": items})
        screens_out[s["id"]] = {"name": s["name"], "rule": s["rule"], "days": days}

    os.makedirs(OUT_DIR, exist_ok=True)
    base = {"generatedAt": now, "source": source, "failedTickers": fails}
    with open(os.path.join(OUT_DIR, "history.json"), "w", encoding="utf-8") as f:
        json.dump({**base, "screens": screens_out}, f, ensure_ascii=False, indent=1)
    latest = {**base, "screens": {k: {**{kk: vv for kk, vv in v.items() if kk != "days"}, **v["days"][-1]}
                                  for k, v in screens_out.items()}}
    with open(os.path.join(OUT_DIR, "latest.json"), "w", encoding="utf-8") as f:
        json.dump(latest, f, ensure_ascii=False, indent=1)
    for k, v in latest["screens"].items():
        print(f"[{v['name']}] {v['date']} {v['count']}종목 / 대상 {v['universe']}종목")
    print(f"source={source}, fails={fails}")
    return latest


def main():
    errors = []
    for fn in (via_naver, via_pykrx):
        try:
            data = fn()
            break
        except Exception as e:  # noqa
            errors.append(f"{fn.__name__}: {e}")
            print("실패:", errors[-1], file=sys.stderr)
    else:
        sys.exit("모든 데이터 소스 실패\n" + "\n".join(errors))
    run(*data)


if __name__ == "__main__":
    main()
