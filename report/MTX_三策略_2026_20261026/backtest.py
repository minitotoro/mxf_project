#!/usr/bin/env python3
"""MTX three-strategy event backtest. Source specifications are the two root Markdown files.

The input is the original MXF1 continuous-month, start-stamped five-minute feed.
The program never fills a missing signal bar or invents a settlement price.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import zipfile
from collections import defaultdict, deque
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import date, datetime, time, timedelta
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path

ORDER = ("開盤空", "尾盤空", "隔夜多")
POINT_VALUE = 50


@dataclass(frozen=True)
class Bar:
    at: datetime
    o: int
    h: int
    l: int
    c: int
    volume: int


@dataclass
class Lot:
    strategy: str
    direction: int
    qty: int
    entry_at: datetime
    entry_raw: int
    entry_fill: int
    entry_tax: int
    entry_fee: int
    contract: str
    rollover_entry: bool = False


@contextmanager
def source_text(path: Path):
    if path.suffix.lower() == ".zip":
        with zipfile.ZipFile(path) as archive:
            if archive.namelist() != ["MXF1_5_minute.txt"]:
                raise ValueError(f"Unexpected ZIP members: {archive.namelist()!r}")
            with archive.open("MXF1_5_minute.txt") as raw, io.TextIOWrapper(raw,encoding="utf-8-sig",newline="") as fh:
                yield fh
    else:
        with path.open(encoding="utf-8-sig",newline="") as fh:
            yield fh


def read_bars(path: Path) -> dict[datetime, Bar]:
    bars = {}
    with source_text(path) as fh:
        reader = csv.DictReader(fh, skipinitialspace=True)
        if reader.fieldnames != ["<Date>", "<Time>", "<Open>", "<High>", "<Low>", "<Close>", "<Volume>"]:
            raise ValueError(f"Unexpected MXF column names: {reader.fieldnames!r}")
        for row in reader:
            at = datetime.strptime(row["<Date>"] + " " + row["<Time>"], "%Y/%m/%d %H:%M:%S")
            values = [int(row[k]) for k in ("<Open>", "<High>", "<Low>", "<Close>", "<Volume>")]
            if at in bars or at.minute % 5 or values[4] < 0 or values[2] > min(values[0], values[3]) or values[1] < max(values[0], values[3]):
                raise ValueError(f"Invalid or duplicate OHLCV: {at} {values}")
            bars[at] = Bar(at, *values)
    return bars


def read_holidays(path: Path) -> set[date]:
    with path.open(encoding="utf-8-sig", newline="") as fh:
        return {date.fromisoformat(r["休市日期"]) for r in csv.DictReader(fh)}


def trading_calendar(first: date, last: date, holidays: set[date], bars: dict[datetime, Bar]) -> list[date]:
    # Saturdays explicitly present as a day session may be traded; 2018 makeup
    # Saturdays without data are excluded by the source specifications.
    day_dates = {t.date() for t in bars if time(8, 45) <= t.time() < time(13, 45)}
    days = []
    d = first
    while d <= last:
        if d not in holidays and (d.weekday() < 5 or (d.weekday() == 5 and d in day_dates)):
            days.append(d)
        d += timedelta(days=1)
    return days


def settlement_dates(days: list[date]) -> set[date]:
    by_month = defaultdict(list)
    for d in days:
        by_month[d.year, d.month].append(d)
    result = set()
    for (y, m), valid in by_month.items():
        first = date(y, m, 1)
        third_wednesday = first + timedelta(days=(2 - first.weekday()) % 7 + 14)
        future = [d for d in valid if d >= third_wednesday]
        if future:
            result.add(future[0])
    return result


def contract_month(day: date, at: datetime, settlements: set[date]) -> str:
    s = next((d for d in settlements if d.year == day.year and d.month == day.month), None)
    if s is None:
        raise ValueError(f"Settlement calendar incomplete: {day}")
    advance = day > s or (day == s and at.time() >= time(13, 30))
    y, m = day.year, day.month + int(advance)
    if m == 13:
        y, m = y + 1, 1
    return f"{y:04d}-{m:02d}"


def excluded_ranges(days: list[date], settlements: set[date], bars: dict[datetime, Bar]):
    gaps = []
    counts = defaultdict(int)
    for t in bars:
        if time(8, 45) <= t.time() < time(13, 45):
            counts[t.date()] += 1
    for d in days:
        expected = 57 if d in settlements else 60
        count = counts[d]
        if count < expected and not (d.weekday() == 5 and count == 0):
            gaps.append((d, count, expected))
    ranges = set()
    for d, _, _ in gaps:
        monday = d - timedelta(days=d.weekday())
        ranges.update(monday + timedelta(days=i) for i in range(-7, 14))
    return gaps, ranges


def tax(price: int) -> int:
    return int((Decimal(price) * Decimal("0.001")).quantize(Decimal("1"), rounding=ROUND_HALF_UP))


def weekday_rule(d: date) -> int:
    return 4 if d.weekday() == 5 else d.weekday()


def run(bars: dict[datetime, Bar], holidays: set[date], year: int, fee: int, slip: int,
        thursday: bool = False, friday: bool = False) -> dict:
    first, last = min(bars).date(), max(bars).date()
    days = trading_calendar(max(first, date(2018, 1, 1)), last, holidays, bars)
    settlement = settlement_dates(days)
    gaps, excluded = excluded_ranges(days, settlement, bars)
    available_sessions = [d for d in days if d.year == year and datetime.combine(d,time(8,45)) in bars]
    if not available_sessions:
        raise ValueError(f"No day sessions found for requested year: {year}")
    sample_end = max(available_sessions)
    evening_marks = {}
    for t, bar in bars.items():
        if time(15) <= t.time() < time(23, 56):
            evening_marks[t.date()] = bar
    index = {d: i for i, d in enumerate(days)}
    lots: list[Lot] = []
    trades, orders, skips, daily_mark = [], [], [], []
    cash = 0
    # Include prior completed days to warm up MA20, then trade only from Jan 1.
    daily_closes = {}
    pending_exit = set()
    pending_roll = False

    def atbar(d, hm):
        return bars.get(datetime.combine(d, time.fromisoformat(hm)))

    def record_skip(d, hm, event, reason):
        skips.append(dict(date=str(d), time=hm, event=event, reason=reason))

    def do_order(strategy, direction, qty, bar, trade_day, kind, rollover=False, contract=None):
        nonlocal cash
        if not bar or qty <= 0:
            return 0
        raw = bar.o
        fill = raw + direction * slip
        per_tax = tax(fill)
        cash -= qty * (per_tax + fee)
        matched = 0
        remaining = qty
        month = contract or contract_month(trade_day, bar.at, settlement)
        for lot in list(lots):
            if remaining == 0:
                break
            if lot.direction == direction or lot.contract != month:
                continue
            q = min(remaining, lot.qty)
            pnl = (fill - lot.entry_fill) * lot.direction * POINT_VALUE * q
            cash += pnl
            trades.append(dict(strategy=lot.strategy, direction="多" if lot.direction == 1 else "空",
                entry_at=lot.entry_at.isoformat(sep=" "), exit_at=bar.at.isoformat(sep=" "),
                entry_raw=lot.entry_raw, exit_raw=raw, entry_fill=lot.entry_fill, exit_fill=fill,
                qty=q, contract=lot.contract, gross=pnl, entry_tax=lot.entry_tax*q,
                exit_tax=per_tax*q, entry_fee=lot.entry_fee*q, exit_fee=fee*q,
                net=pnl-(lot.entry_tax+lot.entry_fee+per_tax+fee)*q,
                holding_minutes=int((bar.at-lot.entry_at).total_seconds()/60),
                exit_reason=kind, rollover_entry=lot.rollover_entry,
                settlement_close=kind=="settlement", gap_close=kind=="gap"))
            lot.qty -= q
            remaining -= q
            matched += q
            if lot.qty == 0:
                lots.remove(lot)
        if remaining:
            if kind not in ("entry", "rollover_entry"):
                raise AssertionError(f"Exit would open an unintended position: {strategy} {bar.at}")
            lots.append(Lot(strategy, direction, remaining, bar.at, raw, fill, per_tax, fee, month, rollover))
        orders.append(dict(at=bar.at.isoformat(sep=" "), trade_day=str(trade_day), strategy=strategy,
            kind=kind, side="買" if direction == 1 else "賣", qty=qty,
            raw=raw, fill=fill, tax=per_tax*qty, fee=fee*qty, matched=matched,
            opened=remaining, contract=month, net_position=sum(x.direction*x.qty for x in lots)))
        return remaining

    def held(strategy):
        return sum(x.qty for x in lots if x.strategy == strategy)

    def close_strategy(strategy, bar, d, reason):
        q = held(strategy)
        if q:
            direction = -next(x.direction for x in lots if x.strategy == strategy)
            do_order(strategy, direction, q, bar, d, reason)

    def execute_or_defer(strategy, bar, d, reason):
        if not held(strategy):
            return
        if bar:
            close_strategy(strategy, bar, d, reason)
        elif reason == "settlement":
            raise RuntimeError(f"Settlement price absent for unclosed expiring position: {d}")
        else:
            pending_exit.add(strategy)
            record_skip(d, "", strategy+" exit", "missing execution bar; defer to next session open")

    def long_allowed(d):
        i = index[d]
        next_day = days[i+1] if i+1 < len(days) else None
        if next_day is None:
            record_skip(d, "", "隔夜多", "next trading date unavailable")
            return False
        return (next_day-d).days - 1 <= 4

    for d in days:
        if d < date(year-1, 10, 1) or d > date(year+1, 1, 15):
            continue
        active = date(year, 1, 1)-timedelta(days=2) <= d <= date(year, 12, 31)
        closing_only = d.year == year+1 and bool(lots)
        in_gap = d in excluded
        settle = d in settlement
        prev = days[index[d]-1] if index[d] else None
        prev_close = daily_closes.get(prev)
        prev20 = [daily_closes[x] for x in days[max(0,index[d]-20):index[d]] if x in daily_closes]
        rule = weekday_rule(d)
        open_day = atbar(d, "08:45:00")

        if active and in_gap and lots:
            # The specification asks for closure at the first excluded day 08:45.
            if not open_day:
                raise RuntimeError(f"Cannot value a position at start of gap exclusion: {d}")
            for strategy in ORDER:
                close_strategy(strategy, open_day, d, "gap")

        # Deferred exits execute at the next available session open, never at an
        # invented bar. Night 15:00 belongs to the following trading date.
        if pending_exit and open_day:
            for strategy in ORDER:
                if strategy in pending_exit:
                    close_strategy(strategy, open_day, d, "deferred_exit")
            pending_exit.clear()

        if (active or closing_only) and not in_gap:
            b09 = atbar(d, "09:00:00")
            b0855 = atbar(d, "08:55:00")
            if held("隔夜多"):
                execute_or_defer("隔夜多", b09, d, "scheduled")
            if closing_only:
                continue
            if b09 and b0855 and open_day and len(prev20)==20:
                if prev_close < sum(prev20)/20 and b0855.c < open_day.o:
                    do_order("開盤空", -1, 1, b09, d, "entry")
            elif any(x is None for x in (b09,b0855,open_day)):
                record_skip(d,"09:00","開盤空","required bar missing")

            if rule == 4 and friday and long_allowed(d):
                b11, b1055 = atbar(d, "11:00:00"), atbar(d, "10:55:00")
                if b11 and b1055 and open_day and prev_close is not None:
                    if b1055.c > open_day.o and b1055.c > prev_close:
                        do_order("隔夜多", 1, 1, b11, d, "entry")
                else:
                    record_skip(d,"11:00","隔夜多 Friday gate 1","required bar missing")

            if not settle and held("開盤空") == 0:
                b1310, b1315 = atbar(d,"13:10:00"), atbar(d,"13:15:00")
                if b1310 and b1315 and prev_close:
                    if b1310.c * 100 <= prev_close * 99:
                        do_order("尾盤空",-1,2,b1315,d,"entry")
                else:
                    record_skip(d,"13:15","尾盤空","required bar missing")

            if settle:
                b1325 = atbar(d,"13:25:00")
                # A still-held intraday long is closed on expiry and re-entered
                # at the new contract's 15:00 opening, subject to the same signal.
                pending_roll = bool(held("隔夜多")) and long_allowed(d)
                for strategy in ORDER:
                    execute_or_defer(strategy,b1325,d,"settlement")
            else:
                b1340 = atbar(d,"13:40:00")
                for strategy in ORDER[:2]:
                    execute_or_defer(strategy,b1340,d,"scheduled")

            if rule in (0,1,2) and long_allowed(d):
                if settle:
                    pending_roll = True
                elif b1340:
                    do_order("隔夜多",1,1,b1340,d,"entry")
                else:
                    record_skip(d,"13:40","隔夜多","execution bar missing")
            elif rule == 4 and friday and long_allowed(d) and not held("隔夜多") and not pending_roll:
                b1335 = atbar(d,"13:35:00")
                previous_four = [daily_closes[x] for x in days[max(0,index[d]-4):index[d]] if x in daily_closes]
                b1340 = atbar(d,"13:40:00")
                if b1335 and len(previous_four)==4 and b1335.c * 5 > sum(previous_four)+b1335.c:
                    if settle:
                        pending_roll = True
                    elif b1340:
                        do_order("隔夜多",1,1,b1340,d,"entry")
                    else:
                        record_skip(d,"13:40","隔夜多 Friday gate 2","execution bar missing")
                elif b1335 is None:
                    record_skip(d,"13:40","隔夜多 Friday gate 2","signal bar missing")

            b15 = atbar(d,"15:00:00")
            if pending_exit and b15:
                for strategy in ORDER:
                    if strategy in pending_exit:
                        close_strategy(strategy,b15,d,"deferred_exit")
                pending_exit.clear()
            if pending_roll:
                if not settle:
                    raise AssertionError("rollover flagged outside settlement")
                if b15:
                    do_order("隔夜多",1,1,b15,d,"rollover_entry",rollover=True,
                             contract=contract_month(d,b15.at,settlement))
                else:
                    record_skip(d,"15:00","隔夜多 rollover","next-contract open missing; entry not refilled")
                pending_roll = False

            if rule == 3 and thursday and long_allowed(d):
                b2255, b23 = atbar(d,"22:55:00"), atbar(d,"23:00:00")
                b15 = atbar(d,"15:00:00")
                dclose = atbar(d,"13:25:00" if settle else "13:40:00")
                if all((b2255,b23,b15,dclose)):
                    if b2255.c > b15.o and b2255.c > dclose.c:
                        do_order("隔夜多",1,1,b23,d,"entry")
                else:
                    record_skip(d,"23:00","隔夜多 Thursday","required bar missing")

        close_bar = atbar(d,"13:25:00" if settle else "13:40:00")
        if close_bar:
            daily_closes[d] = close_bar.c
        # Mark to market with the last available daytime close; settlement day's
        # new-contract night entry remains open and is marked on subsequent bars.
        if active and close_bar:
            mark = evening_marks.get(d,close_bar)
            mark_contract = contract_month(d,mark.at,settlement)
            unrealized = sum((mark.c-x.entry_fill)*x.direction*x.qty*POINT_VALUE for x in lots if x.contract==mark_contract)
            daily_mark.append(dict(date=str(d), cash=cash, unrealized=unrealized, equity=cash+unrealized,
                                   mark_at=mark.at.isoformat(sep=" "),
                                   net_position=sum(x.direction*x.qty for x in lots), excluded=in_gap))

    if lots:
        raise RuntimeError(f"Backtest ended with unclosed positions: {[(x.strategy,x.entry_at) for x in lots]}")
    if pending_exit:
        raise RuntimeError(f"Backtest ended with deferred exits: {sorted(pending_exit)}")
    if sum(t["net"] for t in trades) != cash:
        raise AssertionError("Ledger net P/L and cash do not reconcile")
    return dict(trades=trades, orders=orders, skips=skips, equity=daily_mark,
                gaps=[dict(date=str(d),found=n,expected=e) for d,n,e in gaps if d.year==year],
                excluded_days=[str(d) for d in days if d.year==year and d in excluded],
                settlements=[str(d) for d in sorted(settlement) if d.year==year],
                fee=fee, slippage=slip, thursday=thursday, friday=friday,
                data_rows=len(bars),sample_end=str(sample_end),
                source_latest_timestamp=max(bars).isoformat(sep=" "))


def metrics(trades):
    if not trades:
        return dict(trades=0,contracts=0,net=0,gross=0,win_rate=None,pf=None,max_drawdown=0)
    # FIFO realized trade drawdown, ordered by the closing transaction.
    equity=peak=drawdown=0
    wins=losses=0
    for t in trades:
        equity+=t["net"]
        peak=max(peak,equity)
        drawdown=max(drawdown,peak-equity)
        wins+=max(t["net"],0)
        losses+=min(t["net"],0)
    return dict(trades=len(trades),contracts=sum(t["qty"] for t in trades),
                net=sum(t["net"] for t in trades),gross=sum(t["gross"] for t in trades),
                win_rate=sum(t["net"]>0 for t in trades)/len(trades),
                pf=(wins/-losses if losses else None),max_drawdown=drawdown)


def write_csv(path, rows):
    if not rows:
        path.write_text("date,time,event,reason\n",encoding="utf-8-sig")
        return
    with path.open("w",encoding="utf-8-sig",newline="") as fh:
        writer=csv.DictWriter(fh,fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def file_hash(path):
    digest=hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda:fh.read(1024*1024),b""):
            digest.update(chunk)
    return digest.hexdigest()


def report_markdown(summaries, year, zip_path, holiday_path, thursday, friday):
    b,c=summaries["baseline"],summaries["conservative"]
    last_session=b["sample_end"]
    partial_year=b["partial_year"]
    excluded_span=(f"{min(b['excluded_days'])} 至 {max(b['excluded_days'])}" if b['excluded_days'] else "無")
    def display(v):
        return f"{v:,.0f}" if v is not None else "—"
    def stat(m):
        return f"{display(m['net'])} | {m['trades']} | {m['contracts']} | {m['win_rate']:.1%} | {m['pf']:.2f} | {display(m['max_drawdown'])}"
    lines=[f"# MTX 三策略 {year} 年回測報告", "",
        "## 範圍與口徑", "",
        f"- 訊號日期：{year}-01-01 至 {last_session}；以**進場年**歸屬績效，年底進場依原定規則持有至下一交易日出場。",
        (f"- **{year} 年是不完整年度**；MXF1 的最後一根時間為 {b['source_latest_timestamp']}，最後一個可用日盤交易日為 {last_session}，不得直接與完整年度總損益比較。" if partial_year else f"- {year} 年日盤資料涵蓋至年度最後交易日 {last_session}。"),
        f"- 隔夜多開關：星期四{'開啟' if thursday else '關閉'}、星期五{'開啟' if friday else '關閉'}。每次進場口數：開盤空 1、尾盤空 2、隔夜多 1 口。",
        "- 單位：新臺幣；每點每口 50 元。成交依指定時點的 5 分 K 開盤價，買價加滑價、賣價減滑價；每口每邊扣期交稅與手續費。",
        "- 訊號只讀指定時點前已完成的 K；同時點先出場、後進場。反向成交以同月份合約 FIFO 沖銷，損益歸原進場策略。",
        "- 市價單在成交時點有 K 棒時視為全數成交；歷史 OHLCV 無委託簿，無法重建真實未成交與部分成交。缺必要 K 時跳過並留紀錄。",
        "- 最大回撤：依**已平倉交易淨損益**累計，從歷史高點至低點的最大金額差；不含未實現損益。未指定起始資金，故不計回撤率。",
        "- 勝率為淨損益大於 0 的平倉紀錄占比；PF 為獲利筆數淨利合計除以虧損筆數淨虧合計；交易筆數按 FIFO 已平倉紀錄。",
        "", "## 合併績效（進場年）", "",
        "| 成本情境 | 淨損益 | 交易筆數 | 平倉口數 | 勝率 | PF | 最大已實現回撤 |", "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
        f"| 基準：單邊 30 元＋1 點 | {stat(b['entry_year'])} |",
        f"| 保守：單邊 50 元＋2 點 | {stat(c['entry_year'])} |", "",
        "## 各策略（依進場年）", "",
        "| 成本情境 | 策略 | 淨損益 | 交易筆數 | 平倉口數 | 勝率 | PF | 最大已實現回撤 |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for name,label in (("baseline","基準"),("conservative","保守")):
        for strategy in ORDER:
            lines.append(f"| {label} | {strategy} | {stat(summaries[name]['by_strategy'][strategy])} |")
    lines += ["", "## 月度淨損益（按進場月份）", "",
              "| 月份 | 基準 | 保守 |", "| --- | ---: | ---: |"]
    for m in range(1,13):
        lines.append(f"| {year}-{m:02d} | {display(b['monthly'][f'{m:02d}'])} | {display(c['monthly'][f'{m:02d}'])} |")
    lines += ["", "## 跨年與資料稽核", "",
        f"- 若以**出場年**列報 {year} 年已實現淨損益：基準 {display(b['exit_year']['net'])} 元；保守 {display(c['exit_year']['net'])} 元。它與上表相差跨年進出場，不是成本差異。",
        f"- 逐筆 CSV 為完整核帳流水，另含 {year-1} 年底進場、{year} 年出場，以及 {year} 年底進場、{year+1} 年出場；表格已按各自指定年度篩選。",
        f"- 資料共 {b['source_rows']:,} 根 K；{year} 年休市與結算依指定 CSV。結算日共 {len(b['settlements'])} 天：{', '.join(b['settlements'])}。",
        "- 缺 K 日："+("、".join(f"{x['date']}（{x['found']}/{x['expected']} 根）" for x in b['gaps']) or "無")+"。依缺口週與前後各一週排除交易；實際排除交易日範圍 "+excluded_span+"，共 "+str(len(b['excluded_days']))+" 天。",
        "- 排除期間仍保留檔案內可得的日盤收盤價作為均線歷史；排除的是策略委託，沒有對原始 K 棒補值。",
        f"- 基準／保守缺時點跳過紀錄：{b['skips']}／{c['skips']} 筆。全部逐筆成交、平倉與日終權益見同目錄 CSV。",
        f"- `MXF1_5_minute.zip` SHA-256：`{file_hash(zip_path)}`。",
        f"- 休市 CSV SHA-256：`{file_hash(holiday_path)}`。",
        "", "## 重跑", "", "在儲存庫根目錄執行：", "",
        "```bash", f"python report/MTX_三策略_{year}_20261026/backtest.py \\",
        "  --data MXF1_5_minute.zip \\",
        "  --holidays 2018-2026_台灣期貨市場休市日期_截至20261026.csv \\",
        f"  --year {year} --output report/MTX_三策略_{year}_20261026", "```", "",
        "環境：Python 3.10 以上，僅使用標準函式庫。`--thursday`、`--friday` 可另行開啟兩個隔夜多濾網。", ""]
    return "\n".join(lines)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data",type=Path,required=True)
    parser.add_argument("--holidays",type=Path,required=True)
    parser.add_argument("--year",type=int,default=2025)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--thursday",action="store_true",help="Opt in to Thursday overnight entries")
    parser.add_argument("--friday",action="store_true",help="Opt in to Friday overnight entries")
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    bars,holidays=read_bars(args.data),read_holidays(args.holidays)
    summaries={}
    for name,fee,slip in (("baseline",30,1),("conservative",50,2)):
        result=run(bars,holidays,args.year,fee,slip,args.thursday,args.friday)
        for field in ("trades","orders","skips","equity"):
            write_csv(args.output/f"{name}_{field}.csv",result[field])
        year_trades=[t for t in result["trades"] if t["entry_at"].startswith(str(args.year))]
        exit_trades=[t for t in result["trades"] if t["exit_at"].startswith(str(args.year))]
        monthly={f"{month:02d}":sum(t["net"] for t in year_trades if t["entry_at"].startswith(f"{args.year}-{month:02d}")) for month in range(1,13)}
        summaries[name]={"entry_year":metrics(year_trades),"exit_year":metrics(exit_trades),
            "by_strategy":{s:metrics([t for t in year_trades if t["strategy"]==s]) for s in ORDER},
            "monthly":monthly,
            "gaps":result["gaps"],"excluded_days":result["excluded_days"],
            "settlements":result["settlements"],"skips":len(result["skips"]),
            "orders":len(result["orders"]),"source_rows":result["data_rows"]}
        summaries[name]["sample_end"]=result["sample_end"]
        summaries[name]["source_latest_timestamp"]=result["source_latest_timestamp"]
        summaries[name]["partial_year"]=result["source_latest_timestamp"][:10]<f"{args.year}-12-31"
    (args.output/"summary.json").write_text(json.dumps(summaries,ensure_ascii=False,indent=2),encoding="utf-8")
    (args.output/"README.md").write_text(report_markdown(summaries,args.year,args.data,args.holidays,args.thursday,args.friday),encoding="utf-8")
    print(json.dumps(summaries,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
