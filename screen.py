"""코스피·코스닥 아침 스크리너.

매 거래일 아침 실행하면 직전 거래일까지의 일봉으로 여러 조건(항목)을 계산해
results/latest.json 과 results/history.json 에 저장한다.

항목을 늘리려면: 아래 SCREENS 에 {id, name, fn, rule} 하나를 추가하면 된다.
fn(bars, i) 는 i번째 거래일이 조건에 맞으면 표에 보일 값(dict)을, 아니면 None 을 돌려준다.

데이터: KRX(한국거래소) 정규시장 일봉 — 넥스트레이드 제외. KRX 로그인이 안 되면 네이버 일봉으로 대체(넥스트레이드 포함 가능)
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
BARS = 360          # 받아올 일봉 개수 (52주 신고가 + 주봉 지표 여유, 약 72주)
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


# ================================================================ 항목 3: 박세익 주봉 볼린저 매매
# 출처: 체슬리TV "박세익 전무가 처음 공개하는 필살기 매매 기법" (2025-05-31)
#  매수: 주봉 종가가 볼린저밴드(12, 2) 상단을 새로 돌파 + 주간 거래량 ≥ 직전 20주 평균 × 2
#  매도: 매수 이후 주봉 RSI(14)가 70 아래로 내려올 때
#  보유: 매수 신호 이후 아직 매도 신호가 나오지 않은 상태
SK_N, SK_K, SK_VOLX, SK_VOLN, SK_RSI_N, SK_RSI_LV = 12, 2.0, 2.0, 20, 14, 70.0


def weekly(bars):
    """일봉 → 주봉 (ISO 주 단위). 진행 중인 이번 주도 포함."""
    weeks, key = [], None
    for b in bars:
        y, w, _ = datetime.strptime(b["date"], "%Y-%m-%d").isocalendar()
        if (y, w) != key:
            key = (y, w)
            weeks.append({"date": b["date"], "start": b["date"], "open": b["open"], "high": b["high"],
                          "low": b["low"], "close": b["close"], "volume": b["volume"]})
        else:
            wk = weeks[-1]
            wk["date"] = b["date"]
            wk["high"] = max(wk["high"], b["high"])
            wk["low"] = min(wk["low"], b["low"])
            wk["close"] = b["close"]
            wk["volume"] += b["volume"]
    return weeks


def rsi_series(closes, n=SK_RSI_N):
    """Wilder RSI. 앞쪽 n개는 None."""
    out = [None] * len(closes)
    if len(closes) <= n:
        return out
    gains = [max(closes[k] - closes[k - 1], 0) for k in range(1, len(closes))]
    losses = [max(closes[k - 1] - closes[k], 0) for k in range(1, len(closes))]
    ag, al = sum(gains[:n]) / n, sum(losses[:n]) / n
    def val(g, l):
        return 100.0 if l == 0 else 100 - 100 / (1 + g / l)
    out[n] = val(ag, al)
    for k in range(n + 1, len(closes)):
        ag = (ag * (n - 1) + gains[k - 1]) / n
        al = (al * (n - 1) + losses[k - 1]) / n
        out[k] = val(ag, al)
    return out


def sekik_weekly(bars, i):
    """i번째 거래일까지의 주봉으로 매수/매도/보유 상태를 계산."""
    if bars[i]["volume"] <= 0:
        return None
    wk = weekly(bars[:i + 1])
    n = len(wk)
    if n < SK_VOLN + 2:
        return None
    closes = [w["close"] for w in wk]
    vols = [w["volume"] for w in wk]
    rsi = rsi_series(closes)
    ups = [None] * n
    for k in range(SK_N - 1, n):
        win = closes[k + 1 - SK_N:k + 1]
        m = sum(win) / SK_N
        ups[k] = m + SK_K * math.sqrt(sum((x - m) ** 2 for x in win) / SK_N)

    holding, entry, state = False, None, None
    start = max(SK_N, SK_VOLN, SK_RSI_N + 1)
    for k in range(start, n):
        avgv = sum(vols[k - SK_VOLN:k]) / SK_VOLN
        vr = vols[k] / avgv if avgv else 0
        signal = None
        if not holding:
            if closes[k] > ups[k] and closes[k - 1] <= ups[k - 1] and vr >= SK_VOLX:
                holding, entry, signal = True, k, "buy"
        elif rsi[k - 1] is not None and rsi[k] is not None and rsi[k - 1] >= SK_RSI_LV > rsi[k]:
            holding, signal = False, "sell"
            state = {"signal": "sell", "k": k, "entry": entry}
        if signal == "buy":
            state = {"signal": "buy", "k": k, "entry": entry}
        elif holding and signal is None:
            state = {"signal": "hold", "k": k, "entry": entry}
        elif not holding and signal is None:
            state = None
        # state 는 마지막 주(k = n-1)의 상태만 의미가 있다

    if state is None or state["k"] != n - 1:
        return None
    last, e = wk[-1], wk[state["entry"]]
    avgv = sum(vols[-1 - SK_VOLN:-1]) / SK_VOLN
    row = {
        "signal": state["signal"],
        "close": last["close"],
        "changePct": round((closes[-1] / closes[-2] - 1) * 100, 2) if closes[-2] else None,  # 주간 등락률
        "upper": round(ups[-1], 1),
        "abovePct": round((closes[-1] / ups[-1] - 1) * 100, 2),
        "rsi": round(rsi[-1], 1) if rsi[-1] is not None else None,
        "volume": vols[-1],
        "volRatio": round(vols[-1] / avgv, 2) if avgv else None,
        "tradeValue": int(sum(b["close"] * b["volume"] for b in bars[:i + 1] if b["date"] >= last["start"])),
        "entryWeek": e["start"],
        "entryPrice": e["close"],
        "sinceEntryPct": round((last["close"] / e["close"] - 1) * 100, 2) if e["close"] else None,
        "weeksHeld": (n - 1) - state["entry"],
        "weekStart": last["start"],
        "weekDone": datetime.strptime(last["date"], "%Y-%m-%d").weekday() == 4,
    }
    return row


SCREENS = [
    {"id": "high52", "name": "52주 신고가", "fn": high52,
     "rule": "당일 고가 > 직전 52주(364일) 최고가"},
    {"id": "bb_upper", "name": "볼린저밴드 상단 돌파", "fn": bb_upper,
     "rule": "20일·2σ, 전일 종가 ≤ 상단 → 당일 종가 > 상단"},
    {"id": "sekik_bb", "name": "박세익 주봉 볼린저", "fn": sekik_weekly,
     "rule": "주봉 BB(12,2) 상단 돌파 + 거래량 20주 평균×2 매수 / RSI(14) 70 하향 매도"},
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


# ================================================================ KRX (기본)
def via_krx():
    """KRX(한국거래소) 정규시장 일봉. 넥스트레이드 가격은 섞이지 않는다.
    KRX 정보데이터시스템 로그인이 필요: 환경변수 KRX_ID, KRX_PW (GitHub Secrets)."""
    if not (os.getenv("KRX_ID") and os.getenv("KRX_PW")):
        raise RuntimeError("KRX_ID / KRX_PW 가 설정되지 않음")
    from pykrx import stock
    now = datetime.now(KST)
    today = now.date()
    d = today if now.hour >= 16 else today - timedelta(days=1)
    frames, tried = [], 0
    while len(frames) < BARS - 10 and (today - d).days < 560:
        if d.weekday() < 5:
            tried += 1
            ds = d.strftime("%Y%m%d")
            dfs = {m: stock.get_market_ohlcv(ds, market=m) for m in MARKETS}
            if all(df is not None and len(df) and df["종가"].sum() > 0 for df in dfs.values()):
                frames.append((d.isoformat(), dfs))
            elif tried >= 10 and not frames:
                raise RuntimeError("KRX 에서 시세를 받지 못함 (로그인 정보를 확인하세요)")
            time.sleep(0.15)
        d -= timedelta(days=1)
    frames.reverse()
    if len(frames) < 240:
        raise RuntimeError(f"KRX 에서 충분한 거래일을 받지 못함: {len(frames)}일")
    all_bars, market_of = {}, {}
    for date, dfs in frames:
        for m, df in dfs.items():
            for code, row in df.iterrows():
                market_of[code] = m
                all_bars.setdefault(code, []).append({
                    "date": date, "open": float(row["시가"]), "high": float(row["고가"]),
                    "low": float(row["저가"]), "close": float(row["종가"]), "volume": int(row["거래량"])})
    def name_of(code):
        try:
            return stock.get_market_ticker_name(code)
        except Exception:
            return code
    out = {code: ({"code": code, "name": name_of(code), "market": market_of[code]}, bars)
           for code, bars in all_bars.items()}
    return out, "krx", 0


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
                         **({"countBySignal": {g: sum(1 for r in items if r.get("signal") == g)
                                               for g in ("buy", "sell", "hold")}}
                            if any("signal" in r for r in items) else {}),
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
    for fn in (via_krx, via_naver):
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
