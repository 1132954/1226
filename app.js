"use strict";

/**
 * FinalTerm Go (Human Black, Computer White)
 * FIXES:
 * 1) Two consecutive passes -> AUTO enter scoring mode + show result
 * 2) Better AI: reasonable candidate moves, avoid eye-filling / self-atari, prefer local play
 */

const EMPTY = 0;
const BLACK = 1;
const WHITE = 2;

const boardEl = document.getElementById("board");
const sizeEl = document.getElementById("size");
const handicapEl = document.getElementById("handicap");
const komiEl = document.getElementById("komi");
const passBtn = document.getElementById("passBtn");
const scoreBtn = document.getElementById("scoreBtn");
const resetBtn = document.getElementById("resetBtn");

const turnDot = document.getElementById("turnDot");
const turnText = document.getElementById("turnText");
const modeBadge = document.getElementById("modeBadge");
const capBlackEl = document.getElementById("capBlack");
const capWhiteEl = document.getElementById("capWhite");
const movesEl = document.getElementById("moves");
const hintEl = document.getElementById("hint");
const warnText = document.getElementById("warnText");

// score panel
const bTerEl = document.getElementById("bTer");
const wTerEl = document.getElementById("wTer");
const bPrisEl = document.getElementById("bPris");
const wPrisEl = document.getElementById("wPris");
const komiShowEl = document.getElementById("komiShow");
const bTotalEl = document.getElementById("bTotal");
const wTotalEl = document.getElementById("wTotal");
const resultText = document.getElementById("resultText");
const recalcBtn = document.getElementById("recalcBtn");
const confirmBtn = document.getElementById("confirmBtn");

let N = 9;
let board = [];
let turn = BLACK; // human always BLACK
let captures = { [BLACK]: 0, [WHITE]: 0 };

// Simple Ko: forbid returning to immediate previous position
let lastBoardString = "";
let lastMove = null; // {r,c,color}
let moveHistory = [];
let consecutivePass = 0;

let scoringMode = false;
let deadMarks = new Set(); // "r,c"
let gameEnded = false;
let territoryOwner = null;

let isComputerThinking = false;

// ----------------- helpers -----------------
function opponent(color){ return color === BLACK ? WHITE : BLACK; }
function colorName(color){ return color === BLACK ? "黑" : "白"; }
function keyOf(r,c){ return `${r},${c}`; }
function parseKey(k){ const [r,c]=k.split(",").map(Number); return [r,c]; }
function cloneBoard(b){ return b.map(row => row.slice()); }
function boardToString(b){ return b.map(row => row.join("")).join("|"); }
function inBounds(r,c){ return r>=0 && r<N && c>=0 && c<N; }

function neighbors(r,c){
  const out = [];
  if (r>0) out.push([r-1,c]);
  if (r<N-1) out.push([r+1,c]);
  if (c>0) out.push([r,c-1]);
  if (c<N-1) out.push([r,c+1]);
  return out;
}

function coordLabel(r,c){
  const letters = "ABCDEFGHJKLMNOPQRSTUVWX";
  const col = letters[c] || "?";
  const row = (N - r);
  return `${col}${row}`;
}

function getGroupAndLiberties(b, sr, sc){
  const color = b[sr][sc];
  const q = [[sr, sc]];
  const seen = new Set([keyOf(sr,sc)]);
  const stones = [];
  let liberties = 0;
  const libSeen = new Set();

  while(q.length){
    const [r,c] = q.pop();
    stones.push([r,c]);
    for(const [nr,nc] of neighbors(r,c)){
      const v = b[nr][nc];
      if(v === EMPTY){
        const k = keyOf(nr,nc);
        if(!libSeen.has(k)){
          libSeen.add(k);
          liberties += 1;
        }
      }else if(v === color){
        const k = keyOf(nr,nc);
        if(!seen.has(k)){
          seen.add(k);
          q.push([nr,nc]);
        }
      }
    }
  }
  return { stones, liberties };
}

function removeStones(b, stones){
  for(const [r,c] of stones) b[r][c] = EMPTY;
}

function countStones(){
  let cnt = 0;
  for(let r=0;r<N;r++) for(let c=0;c<N;c++) if(board[r][c]!==EMPTY) cnt++;
  return cnt;
}

function nearestStoneDistance(r,c){
  // Manhattan distance to nearest existing stone; large if empty board
  let best = 1e9;
  for(let i=0;i<N;i++){
    for(let j=0;j<N;j++){
      if(board[i][j]===EMPTY) continue;
      const d = Math.abs(i-r)+Math.abs(j-c);
      if(d < best) best = d;
    }
  }
  return best === 1e9 ? 0 : best;
}

function isEyeFillLike(b, r, c, color){
  // simple eye-ish detection: all orthogonal neighbors are own color (or edge) and move doesn't capture
  // (not perfect, but reduces stupid inside-eye moves)
  for(const [nr,nc] of neighbors(r,c)){
    if(b[nr][nc] !== color) return false;
  }
  return true;
}

// ----------------- handicap -----------------
function handicapPoints(size){
  let d;
  if(size === 9) d = 2;
  else if(size === 13) d = 3;
  else d = 3;

  const max = size - 1;
  const mid = Math.floor(size/2);

  const tl = [d, d];
  const tr = [d, max - d];
  const bl = [max - d, d];
  const br = [max - d, max - d];
  const top = [d, mid];
  const bot = [max - d, mid];
  const left = [mid, d];
  const right = [mid, max - d];
  const center = [mid, mid];

  if(size === 9) return [br, tl, bl, tr, center, left, right, bot, top];
  return [br, tl, bl, tr, right, left, bot, top, center];
}

function applyHandicap(h){
  if(h <= 0) return;
  const pts = handicapPoints(N);
  const k = Math.min(h, pts.length);
  for(let i=0; i<k; i++){
    const [r,c] = pts[i];
    board[r][c] = BLACK;
  }
}

// ----------------- play rules -----------------
function playMove(r,c,color){
  if(!inBounds(r,c)) return { ok:false, msg:"超出棋盤" };
  if(board[r][c] !== EMPTY) return { ok:false, msg:"此處已有棋子" };

  const before = cloneBoard(board);
  const beforeCaps = { ...captures };
  const beforeLastMove = lastMove;

  board[r][c] = color;
  const opp = opponent(color);

  let captured = [];

  // capture
  for(const [nr,nc] of neighbors(r,c)){
    if(board[nr][nc] === opp){
      const g = getGroupAndLiberties(board, nr, nc);
      if(g.liberties === 0){
        captured.push(...g.stones);
        removeStones(board, g.stones);
      }
    }
  }

  // suicide
  const myG = getGroupAndLiberties(board, r, c);
  if(myG.liberties === 0){
    board = before;
    captures = beforeCaps;
    lastMove = beforeLastMove;
    return { ok:false, msg:"不合法：自殺（禁著點）" };
  }

  // simple Ko (immediate repetition)
  const nowStr = boardToString(board);
  if(nowStr === lastBoardString){
    board = before;
    captures = beforeCaps;
    lastMove = beforeLastMove;
    return { ok:false, msg:"不合法：劫（Ko）" };
  }

  // update ko reference
  lastBoardString = boardToString(before);

  if(captured.length){
    captures[color] += captured.length;
  }

  lastMove = { r, c, color };

  return { ok:true, msg: captured.length ? `提子 ${captured.length} 顆` : "落子成功", captured };
}

function isLegalMoveSim(r,c,color){
  if(!inBounds(r,c)) return false;
  if(board[r][c] !== EMPTY) return false;

  const tmp = cloneBoard(board);
  const koRef = lastBoardString;

  // simulate play on tmp
  const before = cloneBoard(tmp);
  tmp[r][c] = color;
  const opp = opponent(color);

  for(const [nr,nc] of neighbors(r,c)){
    if(tmp[nr][nc] === opp){
      const g = getGroupAndLiberties(tmp, nr, nc);
      if(g.liberties === 0) removeStones(tmp, g.stones);
    }
  }

  const myG = getGroupAndLiberties(tmp, r, c);
  if(myG.liberties === 0) return false;

  const nowStr = boardToString(tmp);
  if(nowStr === koRef) return false;

  // ok
  return true;
}

function simCaptureCount(r,c,color){
  if(!inBounds(r,c) || board[r][c]!==EMPTY) return { ok:false, cap:0, selfLib:0 };
  const tmp = cloneBoard(board);
  const koRef = lastBoardString;

  tmp[r][c] = color;
  const opp = opponent(color);
  let cap = 0;

  for(const [nr,nc] of neighbors(r,c)){
    if(tmp[nr][nc] === opp){
      const g = getGroupAndLiberties(tmp, nr, nc);
      if(g.liberties === 0){
        cap += g.stones.length;
        removeStones(tmp, g.stones);
      }
    }
  }

  const myG = getGroupAndLiberties(tmp, r, c);
  if(myG.liberties === 0) return { ok:false, cap:0, selfLib:0 };

  const nowStr = boardToString(tmp);
  if(nowStr === koRef) return { ok:false, cap:0, selfLib:0 };

  return { ok:true, cap, selfLib: myG.liberties };
}

// ----------------- atari warning -----------------
function findAtariGroups(color){
  const seen = new Set();
  const ataris = [];
  for(let r=0;r<N;r++){
    for(let c=0;c<N;c++){
      if(board[r][c] !== color) continue;
      const k = keyOf(r,c);
      if(seen.has(k)) continue;
      const g = getGroupAndLiberties(board, r, c);
      for(const [sr,sc] of g.stones) seen.add(keyOf(sr,sc));
      if(g.liberties === 1) ataris.push(g);
    }
  }
  return ataris;
}

function updateAtariWarning(){
  const bAtari = findAtariGroups(BLACK);
  const wAtari = findAtariGroups(WHITE);
  if(bAtari.length){
    warnText.textContent = "⚠ 黑棋被叫吃（atari）";
  }else if(wAtari.length){
    warnText.textContent = "⚠ 白棋被叫吃（atari）";
  }else{
    warnText.textContent = "";
  }
}

// ----------------- AI (improved) -----------------
function candidateMoves(){
  const cand = new Set();

  // 🔹 9 路專用開局：前 2 手直接限定
  if(countStones() <= 2){
    const mid = Math.floor(N/2); // 4 (0-index)
    cand.add(keyOf(mid, mid));   // 中央 (5,5)

    // 四個 3-3 星位
    cand.add(keyOf(2,2));
    cand.add(keyOf(2,N-3));
    cand.add(keyOf(N-3,2));
    cand.add(keyOf(N-3,N-3));

    return [...cand].map(parseKey)
      .filter(([r,c]) => isLegalMoveSim(r,c,WHITE));
  }

  // 🔹 中盤：只考慮靠近棋子的點（半徑 2）
  const stones = [];
  for(let r=0;r<N;r++){
    for(let c=0;c<N;c++){
      if(board[r][c] !== EMPTY) stones.push([r,c]);
    }
  }

  for(const [sr,sc] of stones){
    for(let dr=-2; dr<=2; dr++){
      for(let dc=-2; dc<=2; dc++){
        const r = sr + dr;
        const c = sc + dc;
        if(!inBounds(r,c)) continue;
        if(board[r][c] !== EMPTY) continue;
        cand.add(keyOf(r,c));
      }
    }
  }

  let arr = [...cand].map(parseKey)
    .filter(([r,c]) => isLegalMoveSim(r,c,WHITE));

  // 🔹 收官：若太少，再放寬
  if(arr.length < 6){
    arr = [];
    for(let r=0;r<N;r++){
      for(let c=0;c<N;c++){
        if(board[r][c]===EMPTY && isLegalMoveSim(r,c,WHITE)){
          arr.push([r,c]);
        }
      }
    }
  }

  return arr;
}

function aiChooseMove(){
  const cands = candidateMoves().filter(([r,c]) => isLegalMoveSim(r,c,WHITE));
  if(!cands.length) return null;

  // 1) capture immediately
  for(const [r,c] of cands){
    const sim = simCaptureCount(r,c,WHITE);
    if(sim.ok && sim.cap > 0) return { r, c };
  }

  // 2) save self if in atari: play any liberty point
  const myAtari = findAtariGroups(WHITE);
  if(myAtari.length){
    const libPoints = new Set();
    for(const [sr,sc] of myAtari[0].stones){
      for(const [nr,nc] of neighbors(sr,sc)){
        if(board[nr][nc] === EMPTY) libPoints.add(keyOf(nr,nc));
      }
    }
    for(const k of libPoints){
      const [r,c] = parseKey(k);
      if(isLegalMoveSim(r,c,WHITE)) return { r, c };
    }
  }

  // 3) evaluate candidates with better heuristics
  let best = null;
  let bestScore = -1e18;

  for(const [r,c] of cands){
    const sc = evaluateAIMove(r,c);
    if(sc > bestScore){
      bestScore = sc;
      best = { r, c };
    }
  }

  // If everything is terrible, pass
  if(bestScore < -2000) return null;
  return best;
}

function evaluateAIMove(r,c){
  const sim = simCaptureCount(r,c,WHITE);
  if(!sim.ok) return -1e18;

  let score = 0;

  // big reward for capture
  score += sim.cap * 2000;

  // avoid self-atari (unless capturing)
  if(sim.cap === 0 && sim.selfLib === 1) score -= 1500;

  // avoid filling own eye
  if(sim.cap === 0){
    const tmp = cloneBoard(board);
    tmp[r][c] = WHITE;
    if(isEyeFillLike(tmp, r,c,WHITE)) score -= 900;
  }

  // prefer local play: closer to existing stones
  const d = nearestStoneDistance(r,c);
  score += (d === 0 ? 20 : (80 - d*18)); // far => penalty

  // prefer center a bit
  const mid = (N-1)/2;
  const distCenter = Math.abs(r-mid)+Math.abs(c-mid);
  score += (N*2 - distCenter) * 2;

  // adjacency/connectivity
  let adj = 0;
  for(const [nr,nc] of neighbors(r,c)){
    if(board[nr][nc] === WHITE) adj += 1;
    if(board[nr][nc] === BLACK) adj += 0.6; // fighting area
  }
  score += adj * 25;

  // try to put black in atari (rough): if move touches a black group with 2 liberties now, good
  for(const [nr,nc] of neighbors(r,c)){
    if(board[nr][nc] === BLACK){
      const g = getGroupAndLiberties(board, nr, nc);
      if(g.liberties === 2) score += 120;
    }
  }

  // small randomness
  score += Math.random() * 5;

  return score;
}

// ----------------- End by passes (AUTO scoring) -----------------
function autoEnterScoringIfNeeded(){
  if(scoringMode || gameEnded) return;
  if(consecutivePass < 2) return;

  // auto enter scoring mode
  scoringMode = true;

  modeBadge.textContent = "計分模式";
  modeBadge.classList.add("score");

  scoreBtn.disabled = false;
  scoreBtn.textContent = "返回對局"; // now acts as toggle back

  recalcBtn.disabled = false;
  confirmBtn.disabled = false;

  hintEl.textContent = "已連續兩次 Pass → 自動進入計分模式。可點棋子標記死子（再點取消），分數會即時更新。";
  recalcScore();
  renderAll();
}

// ----------------- game flow -----------------
function initState(n){
  N = n;
  board = Array.from({ length: N }, () => Array(N).fill(EMPTY));
  captures = { [BLACK]: 0, [WHITE]: 0 };
  lastBoardString = boardToString(board);
  lastMove = null;
  moveHistory = [];
  consecutivePass = 0;

  scoringMode = false;
  deadMarks = new Set();
  gameEnded = false;
  territoryOwner = null;

  turn = BLACK;
  isComputerThinking = false;

  const h = parseInt(handicapEl.value, 10);
  applyHandicap(h);

  // komi default
  if(h > 0) komiEl.value = "0.5";
  else if(String(komiEl.value).trim() === "") komiEl.value = "6.5";
  komiShowEl.textContent = String(Number(komiEl.value || 0));

  // buttons
  scoreBtn.disabled = true;
  scoreBtn.textContent = "計分";
  recalcBtn.disabled = true;
  confirmBtn.disabled = true;

  passBtn.disabled = false;
  sizeEl.disabled = false;
  handicapEl.disabled = false;
  komiEl.disabled = false;

  warnText.textContent = "";
  renderScorePanel(null);

  hintEl.textContent = "黑先手（你）。點交叉點落子；自殺禁手；單劫禁止立刻還原上一盤面。";
  renderAll();
}

function humanClick(r,c){
  if(gameEnded) return;
  if(isComputerThinking) return;

  // ✅【新增】非計分模式、輪到黑棋時：若完全無合法著點 → 自動 Pass
  if(!scoringMode && turn === BLACK && !hasAnyLegalMove(BLACK)){
    addPassToHistory(BLACK);
    turn = WHITE;
    consecutivePass += 1;

    hintEl.textContent = "黑棋無合法著點，自動 Pass。";
    renderAll();
    autoEnterScoringIfNeeded();

    // 若尚未進入計分，讓白棋照常走（或白棋也可能被迫 pass）
    if(!scoringMode){
      setTimeout(computerMove, 140);
    }
    return;
  }

  // ✅ 原本你的計分模式邏輯照舊
  if(scoringMode){
    if(board[r][c] === EMPTY){
      hintEl.textContent = "計分模式：空點顯示圓點數地；要改分數請點棋子標死子。";
      return;
    }
    const k = keyOf(r,c);
    if(deadMarks.has(k)) deadMarks.delete(k);
    else deadMarks.add(k);
    recalcScore();
    return;
  }

  // ⬇ 下面接你原本 humanClick 的「對局落子」內容（不要動）
  // ...
}


  if(turn !== BLACK){
    hintEl.textContent = "目前輪到白棋（電腦）...";
    return;
  }

  const res = playMove(r,c,BLACK);
  if(!res.ok){
    hintEl.textContent = res.msg;
    return;
  }

  consecutivePass = 0;
  addMoveToHistory(BLACK, r,c, res.captured?.length || 0);

  turn = WHITE;
  hintEl.textContent = res.msg;
  renderAll(res.captured);

  setTimeout(computerMove, 140);
}

function computerMove(){
  if(gameEnded || scoringMode) return;
  if(turn !== WHITE) return;

  isComputerThinking = true;
  renderStatus();

  // ✅【新增】白棋若「完全沒有合法著點」→ 自動 Pass
  if(!hasAnyLegalMove(WHITE)){
    addPassToHistory(WHITE);
    turn = BLACK;
    consecutivePass += 1;
    isComputerThinking = false;

    hintEl.textContent = "白棋（電腦）無合法著點，自動 Pass。";
    renderAll();
    autoEnterScoringIfNeeded();
    return;
  }

  const choice = aiChooseMove();

  if(!choice){
    // computer pass
    addPassToHistory(WHITE);
    turn = BLACK;
    consecutivePass += 1;
    isComputerThinking = false;

    hintEl.textContent = "白棋（電腦）Pass。";
    renderAll();
    autoEnterScoringIfNeeded();
    return;
  }

  // ⬇ 原本白棋正常落子的程式碼不動
}


  const { r, c } = choice;
  const res = playMove(r,c,WHITE);
  if(!res.ok){
    // fallback pass (rare)
    addPassToHistory(WHITE);
    turn = BLACK;
    consecutivePass += 1;
    isComputerThinking = false;

    hintEl.textContent = "白棋（電腦）Pass。";
    renderAll();
    autoEnterScoringIfNeeded();
    return;
  }

  consecutivePass = 0;
  addMoveToHistory(WHITE, r,c, res.captured?.length || 0);

  turn = BLACK;
  isComputerThinking = false;

  hintEl.textContent = res.msg ? `白棋：${res.msg}` : "白棋落子";
  renderAll(res.captured);
}

function pass(){
  if(gameEnded) return;
  if(isComputerThinking) return;

  if(scoringMode){
    hintEl.textContent = "計分模式中不可 Pass；請先按『返回對局』退出。";
    return;
  }

  // ✅ 先確認是不是輪到黑棋
  if(turn !== BLACK){
    hintEl.textContent = "目前輪到白棋（電腦），請稍等。";
    return;
  }

  // ✅ 若黑棋已無合法著點，提示被迫 pass（但仍走正常 pass 流程）
  if(!hasAnyLegalMove(BLACK)){
    hintEl.textContent = "黑棋已無合法著點（被迫 Pass）。";
  }

  // ⬇ 接著放你原本 pass() 後半段：addPassToHistory / consecutivePass / autoEnter... 等
  addPassToHistory(BLACK);
  turn = WHITE;
  consecutivePass += 1;

  renderAll();
  autoEnterScoringIfNeeded();

  if(!scoringMode){
    setTimeout(computerMove, 140);
  }
}


function toggleScoringMode(){
  if(gameEnded) return;
  if(isComputerThinking) return;

  scoringMode = !scoringMode;

  if(scoringMode){
    modeBadge.textContent = "計分模式";
    modeBadge.classList.add("score");
    recalcBtn.disabled = false;
    confirmBtn.disabled = false;
    scoreBtn.textContent = "返回對局";
    hintEl.textContent = "計分模式：點棋子標記死子（再點取消）。空地以圓點顯示黑地/白地。";
    recalcScore();
  }else{
    modeBadge.textContent = "對局中";
    modeBadge.classList.remove("score");
    recalcBtn.disabled = true;
    confirmBtn.disabled = true;
    scoreBtn.textContent = "計分";
    territoryOwner = null;
    renderScorePanel(null);
    hintEl.textContent = "已退出計分模式。";
    renderAll();
  }
}

function confirmEnd(){
  if(!scoringMode) return;
  gameEnded = true;

  hintEl.textContent = "已確認終局。";
  scoreBtn.disabled = true;
  passBtn.disabled = true;
  sizeEl.disabled = true;
  handicapEl.disabled = true;
  komiEl.disabled = true;

  modeBadge.textContent = "已終局";
  modeBadge.classList.add("score");
  renderStatus();
}

function reset(){
  initState(parseInt(sizeEl.value, 10));
}

// ----------------- history -----------------
function addMoveToHistory(color, r,c, capCount){
  const moveNo = moveHistory.length + 1;
  const coord = coordLabel(r,c);
  moveHistory.push(`${moveNo}. ${colorName(color)} ${coord}${capCount>0 ? ` x${capCount}` : ""}`);
}
function addPassToHistory(color){
  const moveNo = moveHistory.length + 1;
  moveHistory.push(`${moveNo}. ${colorName(color)} Pass`);
}

// ----------------- scoring -----------------
function recalcScore(){
  const komi = Number(komiEl.value || 0);
  komiShowEl.textContent = String(komi);
  const score = computeScore({ komi });
  renderScorePanel(score);
  renderBoard();
}

function computeScore({ komi }){
  const b = cloneBoard(board);

  let deadBlack = 0, deadWhite = 0;
  for(const k of deadMarks){
    const [r,c] = parseKey(k);
    const v = b[r][c];
    if(v === BLACK) deadBlack++;
    if(v === WHITE) deadWhite++;
    b[r][c] = EMPTY;
  }

  const prisoners = {
    black: captures[BLACK] + deadWhite,
    white: captures[WHITE] + deadBlack
  };

  territoryOwner = Array.from({ length: N }, () => Array(N).fill(EMPTY));
  const seen = new Set();
  let terBlack = 0, terWhite = 0;

  for(let r=0; r<N; r++){
    for(let c=0; c<N; c++){
      if(b[r][c] !== EMPTY) continue;
      const k0 = keyOf(r,c);
      if(seen.has(k0)) continue;

      const q = [[r,c]];
      seen.add(k0);
      const region = [];
      const borderColors = new Set();

      while(q.length){
        const [cr,cc] = q.pop();
        region.push([cr,cc]);
        for(const [nr,nc] of neighbors(cr,cc)){
          const v = b[nr][nc];
          if(v === EMPTY){
            const kk = keyOf(nr,nc);
            if(!seen.has(kk)){
              seen.add(kk);
              q.push([nr,nc]);
            }
          }else{
            borderColors.add(v);
          }
        }
      }

      if(borderColors.size === 1){
        const only = [...borderColors][0];
        for(const [rr,cc] of region) territoryOwner[rr][cc] = only;
        if(only === BLACK) terBlack += region.length;
        if(only === WHITE) terWhite += region.length;
      }else{
        for(const [rr,cc] of region) territoryOwner[rr][cc] = EMPTY;
      }
    }
  }

  const territory = { black: terBlack, white: terWhite };
  const totalBlack = territory.black + prisoners.black;
  const totalWhite = territory.white + prisoners.white + komi;

  const diff = totalBlack - totalWhite;
  let result = "";
  if(Math.abs(diff) < 1e-9) result = "平局";
  else if(diff > 0) result = `黑勝 +${diff.toFixed(1)}`;
  else result = `白勝 +${Math.abs(diff).toFixed(1)}`;

  return {
    territory,
    prisoners,
    total: { black: totalBlack, white: Number(totalWhite.toFixed(1)) },
    resultText: result
  };
}

// ----------------- rendering -----------------
function renderAll(){
  renderBoard();
  renderStatus();
  renderMoves();
  updateAtariWarning();
}

function renderStatus(){
  turnDot.style.background = (turn === BLACK) ? "#111" : "#f2f2f2";
  if(isComputerThinking && turn === WHITE) turnText.textContent = "輪到：白（電腦思考中…）";
  else turnText.textContent = `輪到：${colorName(turn)}`;
  capBlackEl.textContent = String(captures[BLACK]);
  capWhiteEl.textContent = String(captures[WHITE]);
}

function renderMoves(){
  movesEl.innerHTML = "";
  if(moveHistory.length === 0){
    movesEl.innerHTML = `<div style="opacity:.7">（尚無落子）</div>`;
    return;
  }
  for(let i=0; i<moveHistory.length; i++){
    const div = document.createElement("div");
    div.className = "m";
    const left = document.createElement("span");
    left.textContent = moveHistory[i];
    const tag = document.createElement("span");
    tag.className = "tag";
    tag.textContent = (i === moveHistory.length - 1) ? "latest" : "";
    div.appendChild(left);
    div.appendChild(tag);
    movesEl.appendChild(div);
  }
  movesEl.scrollTop = movesEl.scrollHeight;
}

function renderScorePanel(score){
  if(!score){
    bTerEl.textContent = "0";
    wTerEl.textContent = "0";
    bPrisEl.textContent = String(captures[BLACK]);
    wPrisEl.textContent = String(captures[WHITE]);
    bTotalEl.textContent = "0";
    wTotalEl.textContent = "0";
    resultText.textContent = "尚未計分";
    return;
  }
  bTerEl.textContent = String(score.territory.black);
  wTerEl.textContent = String(score.territory.white);
  bPrisEl.textContent = String(score.prisoners.black);
  wPrisEl.textContent = String(score.prisoners.white);
  bTotalEl.textContent = String(score.total.black);
  wTotalEl.textContent = String(score.total.white);
  resultText.textContent = score.resultText;
}

function renderBoard(){
  boardEl.style.setProperty("--n", String(N));
  boardEl.innerHTML = "";
  boardEl.classList.toggle("score-on", scoringMode);

  const intersections = document.createElement("div");
  intersections.className = "intersections";

  for(let r=0; r<N; r++){
    for(let c=0; c<N; c++){
      const pt = document.createElement("div");
      pt.className = "pt";
      pt.dataset.r = String(r);
      pt.dataset.c = String(c);

      // territory dots (scoring mode only, empty only)
      if(scoringMode && territoryOwner && board[r][c] === EMPTY){
        const owner = territoryOwner[r][c];
        const t = document.createElement("div");
        if(owner === BLACK) t.className = "territory black";
        else if(owner === WHITE) t.className = "territory white";
        else t.className = "territory neutral";
        pt.appendChild(t);
      }

      // hover preview only when human can play
      const preview = document.createElement("div");
      preview.className = "preview black";
      preview.style.display = (!scoringMode && !gameEnded && !isComputerThinking && turn === BLACK) ? "block" : "none";
      pt.appendChild(preview);

      const v = board[r][c];
      if(v !== EMPTY){
        const stone = document.createElement("div");
        stone.className = `stone ${v === BLACK ? "black" : "white"}`;

        if(lastMove && lastMove.r === r && lastMove.c === c && !scoringMode){
          stone.classList.add("lastmove");
        }
        if(scoringMode && deadMarks.has(keyOf(r,c))){
          stone.classList.add("dead");
        }

        pt.appendChild(stone);
      }

      pt.addEventListener("click", () => {
        const rr = parseInt(pt.dataset.r, 10);
        const cc = parseInt(pt.dataset.c, 10);
        humanClick(rr, cc);
      });

      intersections.appendChild(pt);
    }
  }

  boardEl.appendChild(intersections);
}

// ----------------- events -----------------
sizeEl.addEventListener("change", reset);
handicapEl.addEventListener("change", reset);

passBtn.addEventListener("click", pass);
resetBtn.addEventListener("click", reset);

scoreBtn.addEventListener("click", () => {
  // allow manual toggle after auto scoring
  if(consecutivePass >= 2 || scoringMode) toggleScoringMode();
  else hintEl.textContent = "需連續兩次 Pass 後才能計分。";
});

recalcBtn.addEventListener("click", recalcScore);
confirmBtn.addEventListener("click", confirmEnd);

komiEl.addEventListener("input", () => {
  komiShowEl.textContent = String(Number(komiEl.value || 0));
  if(scoringMode) recalcScore();
});
function hasAnyLegalMove(color){
  for(let r=0; r<N; r++){
    for(let c=0; c<N; c++){
      if(board[r][c] !== EMPTY) continue;
      if(isLegalMoveSim(r,c,color)) return true;
    }
  }
  return false;
}
function hasAnyLegalMove(color){
  for(let r=0; r<N; r++){
    for(let c=0; c<N; c++){
      if(board[r][c] !== EMPTY) continue;
      if(isLegalMoveSim(r,c,color)) return true;
    }
  }
  return false;
}


// init
resetUIState();
initState(parseInt(sizeEl.value, 10));

