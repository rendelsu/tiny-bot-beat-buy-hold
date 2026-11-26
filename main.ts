// tiny-bot-beat-buy-hold: a deterministic trend-momentum rotation bot for
// agent-fun/bars-replay/v1. It reads hello/batch lines on stdin and answers
// each batch with one reply of buy/sell orders. Orders decided on bar k fill
// at bar k+1's open. Strategy: stay in cash until a symbol shows a clear
// uptrend (close above its slow EMA by 0.3%, fast EMA above slow EMA, and
// 12-bar momentum above +0.5%, plus positive 24-bar momentum once 24 bars
// of history exist); hold up to three such symbols near 23% of equity each;
// exit on a wide hysteresis break (close 1.5% under the slow EMA or 12-bar
// momentum below -3%) or when a position falls 6% under its cost; rotate
// and trim only on rebalance bars every 4 bars, with a 150 USDC minimum
// trade and a 4%-of-equity drift band. No clock, no environment, no random
// source: the same bars always produce the same replies.

import { createInterface } from 'node:readline';

const FAST_N = 5;
const SLOW_N = 16;
const MOM_N = 12;
const MOM_LONG_N = 24;
const TOP_K = 3;
const TARGET_BPS = 2300n;
const DRIFT_BPS = 400n;
const MAX_SLIPPAGE_BPS = 800;
const REBAL_EVERY = 4;
const ENTRY_SLOW_FACTOR = 1.003;
const ENTRY_MOMENTUM = 0.005;
const EXIT_SLOW_FACTOR = 0.985;
const EXIT_MOMENTUM = -0.03;
const STOP_NUM = 94n;
const STOP_DEN = 100n;
const BPS_DEN = 10000n;

let hello = null;
let warmupBars = 0;
let symInfo = {};
let closes = {};
let emaFast = {};
let emaSlow = {};
let lastCloseRaw = {};
let orderCounter = 0;

function pow10(n) {
  let r = 1n;
  for (let i = 0; i < n; i++) r *= 10n;
  return r;
}

function valueQuote(qty, priceRaw, info) {
  return (qty * priceRaw * pow10(hello.capital.quote_scale)) / pow10(info.qtyScale + info.priceScale);
}

function qtyForValue(value, priceRaw, info) {
  if (priceRaw <= 0n) return 0n;
  return (value * pow10(info.qtyScale + info.priceScale)) / (priceRaw * pow10(hello.capital.quote_scale));
}

function momentumN(sym, n) {
  const h = closes[sym];
  if (!h || h.length <= n) return null;
  const last = h[h.length - 1];
  const base = h[h.length - 1 - n];
  if (!(base > 0)) return null;
  return last / base - 1;
}

function isEligible(sym) {
  const h = closes[sym];
  if (!h || h.length <= MOM_N) return false;
  const c = h[h.length - 1];
  if (!(c > emaSlow[sym] * ENTRY_SLOW_FACTOR)) return false;
  if (!(emaFast[sym] > emaSlow[sym])) return false;
  const m12 = momentumN(sym, MOM_N);
  if (m12 === null || !(m12 > ENTRY_MOMENTUM)) return false;
  if (h.length > MOM_LONG_N) {
    const m24 = momentumN(sym, MOM_LONG_N);
    if (m24 === null || !(m24 > 0)) return false;
  }
  return true;
}

function rankedTargets(present) {
  const cand = [];
  for (const sym of Object.keys(symInfo)) {
    if (present[sym] && isEligible(sym)) cand.push(sym);
  }
  cand.sort((a, b) => {
    const d = momentumN(b, MOM_N) - momentumN(a, MOM_N);
    if (d !== 0) return d;
    return a < b ? -1 : a > b ? 1 : 0;
  });
  return cand.slice(0, TOP_K);
}

function nextClientId(seq) {
  orderCounter += 1;
  return 'o' + seq + '-' + orderCounter;
}

function decide(batch) {
  const seq = batch.seq;
  const present = {};
  for (const bar of batch.bars) {
    const info = symInfo[bar.symbol];
    if (!info) continue;
    present[bar.symbol] = true;
    const raw = BigInt(bar.c);
    lastCloseRaw[bar.symbol] = raw;
    const c = Number(raw) / Math.pow(10, info.priceScale);
    if (!closes[bar.symbol]) {
      closes[bar.symbol] = [];
      emaFast[bar.symbol] = c;
      emaSlow[bar.symbol] = c;
    } else {
      emaFast[bar.symbol] += (2 / (FAST_N + 1)) * (c - emaFast[bar.symbol]);
      emaSlow[bar.symbol] += (2 / (SLOW_N + 1)) * (c - emaSlow[bar.symbol]);
    }
    closes[bar.symbol].push(c);
  }

  if (seq < warmupBars) return [];

  const account = batch.account;
  const cash = BigInt(account.cash_quote_units);
  const equity = BigInt(account.equity_quote_units);
  if (equity <= 0n) return [];

  const heldQty = {};
  const heldCost = {};
  for (const p of account.positions) {
    heldQty[p.symbol] = BigInt(p.qty);
    heldCost[p.symbol] = p.cost_quote_units ? BigInt(p.cost_quote_units) : 0n;
  }
  const heldSyms = Object.keys(heldQty).filter((s) => heldQty[s] > 0n).sort();

  const minNotional = BigInt(hello.fees.min_notional_quote_units);
  const minBuy = 150n * pow10(hello.capital.quote_scale);
  const minTrade = minNotional > minBuy ? minNotional : minBuy;
  const targetValue = (equity * TARGET_BPS) / BPS_DEN;
  const driftBand = (equity * DRIFT_BPS) / BPS_DEN;
  const weightCap = (equity * BigInt(hello.caps.max_weight_bps)) / BPS_DEN;
  const maxOrders = hello.caps.max_orders_per_bar;
  const maxOpen = hello.caps.max_open_positions;

  const targets = rankedTargets(present);
  const targetSet = {};
  for (const s of targets) targetSet[s] = true;

  const orders = [];
  const soldQty = {};
  const soldFull = {};
  const boughtNotional = {};
  let cashLeft = cash;
  let openCount = heldSyms.length;
  let newBuys = 0;

  function pushSell(sym, qty) {
    if (qty <= 0n) return;
    const already = soldQty[sym] || 0n;
    if (already + qty > heldQty[sym]) qty = heldQty[sym] - already;
    if (qty <= 0n) return;
    orders.push({ side: 'sell', client_id: nextClientId(seq), symbol: sym, qty: qty.toString(), max_slippage_bps: MAX_SLIPPAGE_BPS });
    soldQty[sym] = already + qty;
    if (soldQty[sym] >= heldQty[sym]) soldFull[sym] = true;
  }

  // Risk exits run on every bar.
  for (const sym of heldSyms) {
    if (!present[sym]) continue;
    const h = closes[sym];
    const c = h[h.length - 1];
    const m12 = momentumN(sym, MOM_N);
    let exitNow = c < emaSlow[sym] * EXIT_SLOW_FACTOR || (m12 !== null && m12 < EXIT_MOMENTUM);
    if (!exitNow && heldCost[sym] > 0n) {
      const value = valueQuote(heldQty[sym], lastCloseRaw[sym], symInfo[sym]);
      if (value * STOP_DEN < heldCost[sym] * STOP_NUM) exitNow = true;
    }
    if (exitNow) pushSell(sym, heldQty[sym]);
  }

  const isRebalance = seq % REBAL_EVERY === 0;

  if (isRebalance) {
    for (const sym of heldSyms) {
      if (!targetSet[sym] && !soldFull[sym] && present[sym]) pushSell(sym, heldQty[sym]);
    }
    for (const sym of heldSyms) {
      if (!targetSet[sym] || soldFull[sym] || !present[sym]) continue;
      const info = symInfo[sym];
      const value = valueQuote(heldQty[sym], lastCloseRaw[sym], info);
      const excess = value - targetValue;
      if (excess > driftBand && excess >= minTrade) {
        pushSell(sym, qtyForValue(excess, lastCloseRaw[sym], info));
      }
    }
    for (const sym of targets) {
      if (!present[sym] || soldFull[sym] || soldQty[sym]) continue;
      const info = symInfo[sym];
      const held = heldQty[sym] || 0n;
      const heldValue = held > 0n ? valueQuote(held, lastCloseRaw[sym], info) : 0n;
      const need = targetValue - heldValue;
      if (need < minTrade) continue;
      const room = weightCap - heldValue - (boughtNotional[sym] || 0n);
      let buy = need;
      if (buy > room) buy = room;
      if (buy > cashLeft) buy = cashLeft;
      if (buy < minTrade) continue;
      if (held === 0n && openCount + newBuys >= maxOpen) continue;
      orders.push({ side: 'buy', client_id: nextClientId(seq), symbol: sym, notional_quote_units: buy.toString(), max_slippage_bps: MAX_SLIPPAGE_BPS });
      boughtNotional[sym] = (boughtNotional[sym] || 0n) + buy;
      cashLeft -= buy;
      if (held === 0n) newBuys += 1;
    }
  }

  return orders.slice(0, maxOrders);
}

const rl = createInterface({ input: process.stdin, crlfDelay: Infinity });
rl.on('line', (line) => {
  const text = line.trim();
  if (text.length === 0) return;
  let msg;
  try {
    msg = JSON.parse(text);
  } catch (e) {
    return;
  }
  if (msg.type === 'hello') {
    hello = msg;
    warmupBars = typeof msg.warmup_bars === 'number' ? msg.warmup_bars : 0;
    symInfo = {};
    for (const s of msg.symbols) {
      symInfo[s.symbol] = { priceScale: s.price_scale, qtyScale: s.qty_scale };
    }
    return;
  }
  if (msg.type === 'batch') {
    let orders = [];
    try {
      orders = decide(msg);
    } catch (e) {
      orders = [];
    }
    process.stdout.write(JSON.stringify({ type: 'reply', seq: msg.seq, orders: orders }) + '\n');
  }
});
