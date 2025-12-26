"use strict";

/**
 * FinalTerm Go (Human Black, Computer White)
 * - Play on intersections (grid)
 * - Captures, suicide illegal, simple ko (no immediate repetition)
 * - Handicap placement (standard points for 9/13/19)
 * - End: two consecutive passes -> scoring mode
 * - Scoring: Japanese style (territory + prisoners + dead stones + komi for White)
 * - Life/death: user marks dead stones in scoring mode
 * - AI: simple heuristic (capture > save atari > atari opponent > centerish random legal)
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
let lastBoardString = ""; // for simple ko: forbid immediate repetition of previous board position
let lastMove = null;      // {r,c,color}
let moveHistory = [];
let consecutivePass = 0;

let scoringMode = false;
let deadMarks = new Set();     // "r,c"
let gameEnded = false;
let territoryOwner = null;     // 2D owners for empty points in scoring mode

let isComputerThinking = false;

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

function coordLabel(r,c){
  // common Go coords skip I
  const letters = "ABCDEFGHJKLMNOPQRSTUVWX";
  const col = letters[c] || "?";
  const row = (N - r);
  return `${col}${row}`;
}

/* =========================
   Handicap points
   ========================= */
function handicapPoints(size){
  // standard hoshi-ish points for 9/13/19
  // returns list of points in standard placement order (as most GUIs do)
  // order: 4 corners, sides, center, etc.
  let d;
  if(size === 9) d = 2;      // 3-3
  else if(size === 13) d = 3; // 4-4
  else d = 3;                // 4-4 (19)
  const max = size - 1;

  const tl = [d, d];
  const tr = [d, max - d];
  const bl = [max - d, d];
  const br = [max - d, max - d];

  const mid = Math.floor(size/2);
  const top = [d, mid];
  const bot = [max - d, mid];
  const left = [mid, d];
  const right = [mid, max - d];
  const center = [mid, mid];

  // typical order for handicap: 4 corners then sides then center
  if(size === 9){
    return [br, tl, bl, tr, center, left, right, bot, top];
  }
  // 13/19
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

/* =========================
   Legal move + play (with captures, suicide, ko)
   ========================= */
function playMove(r,c,color, { animateCaptures=false } = {}){
  if(!inBounds(r,c)) return { ok:false, msg:"超出棋盤" };
  if(board[r][c] !== EMPTY) return { ok:false, msg:"此處已有棋子" };

  const before = cloneBoard(board);
  const beforeCaptures = { ...captures };
  const beforeLastMove = lastMove;

  board[r][c] = color;
  const opp = opponent(color);

  // capture opponent groups with 0 liberties
  let captured = [];
  for(const [nr,nc] of neighbors(r,c)){
    if(board[nr][nc] === opp){
      const g = getGroupAndLiberties(board, nr, nc);
      if(g.liberties === 0){
        captured.push(...g.stones);
        removeStones(board, g.stones);
      }
    }
  }

  // suicide check
  const myG = getGroupAndLiberties(board, r, c);
  if(myG.liberties === 0){
    board = before;
    captures = beforeCaptures;
    lastMove = beforeLastMove;
    return { ok:false, msg:"不合法：自殺（禁著點）" };
  }

  // simple ko check: forbid returning to immediate previous position
  const nowStr = boardToString(board);
  if(nowStr === lastBoardString){
    board = before;
    captures = beforeCaptures;
    lastMove = beforeLastMove;
    return { ok:false, msg:"不合法：劫（Ko）" };
  }

  // update ko reference: previous board becomes lastBoardString
  lastBoardString = boardToString(before);

  if(captured.length){
    captures[color] += captured.length;
  }

  lastMove = { r, c, color };

  // animation marker for captured stones: store in DOM after render (we do after render via captured list)
  return { ok:true, msg: captured.length ? `提子 ${captured.length} 顆` : "落子成功", captured };
}

function isLegalMove(r,c,color){
  const tmp = cloneBoard(board);
  const tmpCaps = { ...captures };
  const tmpLast = lastMove;
  const tmpKo = lastBoardString;

  // simulate
  const res = playMove_sim(tmp, tmpKo, r, c, color);
  // restore not needed since using tmp
  return res.ok;
}

function playMove_sim(tmpBoard, koRef, r,c,color){
  if(!inBounds(r,c)) return { ok:false };
  if(tmpBoard[r][c] !== EMPTY) return { ok:false };
  const before = cloneBoard(tmpBoard);

  tmpBoard[r][c] = color;
  const opp = opponent(color);

  // capture
  for(const [nr,nc] of neighbors(r,c)){
    if(tmpBoard[nr][nc] === opp){
      const g = getGroupAndLiberties(tmpBoard, nr, nc);
      if(g.liberties === 0) removeStones(tmpBoard, g.stones);
    }
  }

  // suicide
  const myG = getGroupAndLiberties(tmpBoard, r, c);
  if(myG.liberties === 0) return { ok:false };

  // ko
  const nowStr = boardToString(tmpBoard);
  if(nowStr === koRef) return { ok:false };

  return { ok:true };
}

/* =========================
   Atari warning (叫吃)
   ========================= */
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

/* =========================
   AI (White)
   ========================= */
function aiChooseMove(){
  // return {r,c} or null for pass
  const legalMoves = [];
  for(let r=0;r<N;r++){
    for(let c=0;c<N;c++){
      if(board[r][c] !== EMPTY) continue;
      if(playMove_sim(cloneBoard(board), lastBoardString, r, c, WHITE).ok){
        legalMoves.push([r,c]);
      }
    }
  }
  if(!legalMoves.length) return null;

  // 1) capture immediately
  for(const [r,c] of legalMoves){
    const tmp = cloneBoard(board);
    const res = playMove_sim_captureCount(tmp, lastBoardString, r,c,WHITE);
    if(res.ok && res.capturedCount > 0) return { r, c };
  }

  // 2) save self if in atari: try moves that increase liberties for an atari group
  const myAtari = findAtariGroups(WHITE);
  if(myAtari.length){
    const target = myAtari[0];
    const [lr,lc] = target.stones[0];
    // try legal moves that connect/defend around that group
    const candidates = new Set();
    for(const [sr,sc] of target.stones){
      for(const [nr,nc] of neighbors(sr,sc)){
        if(board[nr][nc] === EMPTY) candidates.add(keyOf(nr,nc));
      }
    }
    const candArr = [...candidates].map(parseKey).filter(([r,c]) => playMove_sim(cloneBoard(board), lastBoardString, r,c,WHITE).ok);
    if(candArr.length) return { r: candArr[0][0], c: candArr[0][1] };
  }

  // 3) put opponent in atari / attack: find move that reduces black group liberties to 1 or captures next
  let best = null;
  let bestScore = -1e9;
  for(const [r,c] of legalMoves){
    const score = evaluateMove(r,c,WHITE);
    if(score > bestScore){
      bestScore = score;
      best = { r, c };
    }
  }
  return best ?? { r: legalMoves[0][0], c: legalMoves[0][1] };
}

function playMove_sim_captureCount(tmpBoard, koRef, r,c,color){
  if(!inBounds(r,c)) return { ok:false, capturedCount:0 };
  if(tmpBoard[r][c] !== EMPTY) return { ok:false, capturedCount:0 };

  tmpBoard[r][c] = color;
  const opp = opponent(color);
  let cap = 0;

  for(const [nr,nc] of neighbors(r,c)){
    if(tmpBoard[nr][nc] === opp){
      const g = getGroupAndLiberties(tmpBoard, nr, nc);
      if(g.liberties === 0){
        cap += g.stones.length;
        removeStones(tmpBoard, g.stones);
      }
    }
  }
  const myG = getGroupAndLiberties(tmpBoard, r, c);
  if(myG.liberties === 0) return { ok:false, capturedCount:0 };

  const nowStr = boardToString(tmpBoard);
  if(nowStr === koRef) return { ok:false, capturedCount:0 };

  return { ok:true, capturedCount: cap };
}

function evaluateMove(r,c,color){
  // heuristic: capture > make opponent atari > center preference > connectivity
  const tmp = cloneBoard(board);
  const sim = playMove_sim_captureCount(tmp, lastBoardString, r,c,color);
  if(!sim.ok) return -1e9;

  let score = 0;
  score += sim.capturedCount * 1000;

  // after playing, count if any black group is in atari
  const tmp2 = cloneBoard(board);
  tmp2[r][c] = color;
  const opp = opponent(color);
  // remove captured for more realistic
  for(const [nr,nc] of neighbors(r,c)){
    if(tmp2[nr][nc] === opp){
      const g = getGroupAndLiberties(tmp2, nr, nc);
      if(g.liberties === 0) removeStones(tmp2, g.stones);
    }
  }
  let atariCount = 0;
  const seen = new Set();
  for(let i=0;i<N;i++){
    for(let j=0;j<N;j++){
      if(tmp2[i][j] !== opp) continue;
      const k = `${i},${j}`;
      if(seen.has(k)) continue;
      const g = getGroupAndLiberties(tmp2, i, j);
      for(const [sr,sc] of g.stones) seen.add(`${sr},${sc}`);
      if(g.liberties === 1) atariCount++;
    }
  }
  score += atariCount * 60;

  // center preference
  const mid = (N-1)/2;
  const dist = Math.abs(r-mid) + Math.abs(c-mid);
  score += (N - dist) * 2;

  // adjacency (connect / expand)
  let adj = 0;
  for(const [nr,nc] of neighbors(r,c)){
    if(board[nr][nc] === color) adj += 1;
  }
  score += adj * 8;

  // small randomness to avoid identical play
  score += Math.random() * 2;

  return score;
}

/* =========================
   Game flow
   ========================= */
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

  turn = BLACK; // always start black (human)
  isComputerThinking = false;

  // apply handicap
  const h = parseInt(handicapEl.value, 10);
  applyHandicap(h);

  // common practice: with handicap, komi is 0.5 (or 0). Here we set 0.5 by default.
  if(h > 0){
    komiEl.value = "0.5";
  }else{
    if(String(komiEl.value).trim() === "") komiEl.value = "6.5";
  }
  komiShowEl.textContent = String(Number(komiEl.value || 0));

  renderAll();
  scoreBtn.disabled = true;
  recalcBtn.disabled = true;
  confirmBtn.disabled = true;

  passBtn.disabled = false;
  sizeEl.disabled = false;
  handicapEl.disabled = false;
  komiEl.disabled = false;

  hintEl.textContent = "黑先手（你）。點交叉點落子；自殺禁手；單劫禁止立刻還原上一盤面。";
}

function humanClick(r,c){
  if(gameEnded) return;
  if(isComputerThinking) return;

  if(scoringMode){
    // mark dead stones
    if(board[r][c] === EMPTY){
      hintEl.textContent = "計分模式：空點顯示圓點數地。要改分數請點棋子標死子。";
      return;
    }
    const k = keyOf(r,c);
    if(deadMarks.has(k)) deadMarks.delete(k);
    else deadMarks.add(k);
    recalcScore();
    return;
  }

  // only allow human when turn = BLACK
  if(turn !== BLACK){
    hintEl.textContent = "目前輪到白棋（電腦）...";
    return;
  }

  const res = playMove(r,c,BLACK, { animateCaptures:true });
  if(!res.ok){
    hintEl.textContent = res.msg;
    return;
  }

  consecutivePass = 0;
  addMoveToHistory(BLACK, r,c, res.captured?.length || 0);

  // switch to white
  turn = WHITE;
  warnText.textContent = "";
  hintEl.textContent = res.msg;
  renderAll(res.captured);

  // computer respond
  setTimeout(computerMove, 120);
}

function computerMove(){
  if(gameEnded || scoringMode) return;
  if(turn !== WHITE) return;

  isComputerThinking = true;
  renderStatus();

  const choice = aiChooseMove();
  if(!choice){
    // pass
    addPassToHistory(WHITE);
    turn = BLACK;
    consecutivePass += 1;
    hintEl.textContent = "白棋（電腦）Pass。";
    isComputerThinking = false;

    if(consecutivePass >= 2){
      scoreBtn.disabled = false;
      hintEl.textContent = "已連續兩次 Pass。可按『計分』進入終局計分（點棋子標死子）。";
    }
    renderAll();
    return;
  }

  const { r, c } = choice;
  const res = playMove(r,c,WHITE, { animateCaptures:true });
  if(!res.ok){
    // fallback: if somehow illegal due to race/ko, pass
    addPassToHistory(WHITE);
    turn = BLACK;
    consecutivePass += 1;
    hintEl.textContent = "白棋（電腦）Pass。";
    isComputerThinking = false;
    renderAll();
    return;
  }

  consecutivePass = 0;
  addMoveToHistory(WHITE, r,c, res.captured?.length || 0);
  turn = BLACK;
  isComputerThinking = false;

  hintEl.textContent = res.msg ? `白棋：${res.msg}` : "白棋落子";
  renderAll(res.captured);

  // atari warning for UX: show if black has group in atari or white in atari
  updateAtariWarning();
}

function updateAtariWarning(){
  const bAtari = findAtariGroups(BLACK);
  const wAtari = findAtariGroups(WHITE);
  if(bAtari.length){
    warnText.textContent = "⚠ 黑棋有被叫吃（atari）";
  }else if(wAtari.length){
    warnText.textContent = "⚠ 白棋有被叫吃（atari）";
  }else{
    warnText.textContent = "";
  }
}

function pass(){
  if(gameEnded) return;
  if(isComputerThinking) return;

  if(scoringMode){
    hintEl.textContent = "計分模式中不可 Pass；請先退出計分模式。";
    return;
  }
  if(turn !== BLACK){
    hintEl.textContent = "目前輪到白棋（電腦），請稍等。";
    return;
  }

  addPassToHistory(BLACK);
  turn = WHITE;
  consecutivePass += 1;

  if(consecutivePass >= 2){
    scoreBtn.disabled = false;
    hintEl.textContent = "已連續兩次 Pass。可按『計分』進入終局計分（點棋子標死子）。";
    renderAll();
    return;
  }else{
    hintEl.textContent = "黑棋 Pass。";
  }
  renderAll();
  setTimeout(computerMove, 120);
}

function toggleScoringMode(){
  if(gameEnded) return;
  if(isComputerThinking) return;

  if(!scoringMode && consecutivePass < 2){
    hintEl.textContent = "需連續兩次 Pass 後才能計分。";
    return;
  }

  scoringMode = !scoringMode;

  if(scoringMode){
    modeBadge.textContent = "計分模式";
    modeBadge.classList.add("score");
    recalcBtn.disabled = false;
    confirmBtn.disabled = false;
    scoreBtn.textContent = "返回對局";
    hintEl.textContent = "計分模式：點棋子標記死子（再點一次取消）。空地以圓點顯示黑地/白地。";
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
  scoreBtn.disabled = true;
  initState(parseInt(sizeEl.value, 10));
}

/* =========================
   History UI
   ========================= */
function addMoveToHistory(color, r,c, capCount){
  const moveNo = moveHistory.length + 1;
  const coord = coordLabel(r,c);
  moveHistory.push(`${moveNo}. ${colorName(color)} ${coord}${capCount>0 ? ` x${capCount}` : ""}`);
}
function addPassToHistory(color){
  const moveNo = moveHistory.length + 1;
  moveHistory.push(`${moveNo}. ${colorName(color)} Pass`);
}

/* =========================
   Scoring (Japanese style)
   ========================= */
function recalcScore(){
  const komi = Number(komiEl.value || 0);
  komiShowEl.textContent = String(komi);
  const score = computeScore({ komi });
  renderScorePanel(score);
  renderBoard(); // refresh territory dots
}

function computeScore({ komi }){
  const b = cloneBoard(board);

  // remove dead stones => count as prisoners for opponent
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

  // territory calculation
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

/* =========================
   Rendering
   ========================= */
function renderAll(capturedList){
  renderBoard(capturedList);
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

function renderBoard(capturedList = []){
  boardEl.style.setProperty("--n", String(N));
  boardEl.innerHTML = "";
  boardEl.classList.toggle("score-on", scoringMode);

  const intersections = document.createElement("div");
  intersections.className = "intersections";

  const capturedSet = new Set(capturedList.map(([r,c]) => keyOf(r,c)));

  for(let r=0; r<N; r++){
    for(let c=0; c<N; c++){
      const pt = document.createElement("div");
      pt.className = "pt";
      pt.dataset.r = String(r);
      pt.dataset.c = String(c);

      // territory dots in scoring mode (empty points only)
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
      preview.className = `preview ${BLACK === BLACK ? "black" : "white"}`;
      preview.style.display = (!scoringMode && !gameEnded && !isComputerThinking && turn === BLACK) ? "block" : "none";
      pt.appendChild(preview);

      // stones
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

        // captured animation marker (only for immediate render cycle)
        if(capturedSet.has(keyOf(r,c))){
          stone.classList.add("captured-anim");
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

/* =========================
   Events
   ========================= */
sizeEl.addEventListener("change", reset);
handicapEl.addEventListener("change", reset);

passBtn.addEventListener("click", pass);
resetBtn.addEventListener("click", reset);

scoreBtn.addEventListener("click", toggleScoringMode);
recalcBtn.addEventListener("click", recalcScore);
confirmBtn.addEventListener("click", confirmEnd);

komiEl.addEventListener("input", () => {
  komiShowEl.textContent = String(Number(komiEl.value || 0));
  if(scoringMode) recalcScore();
});

/* enable score button after two passes */
function maybeEnableScoring(){
  if(consecutivePass >= 2){
    scoreBtn.disabled = false;
  }else{
    scoreBtn.disabled = true;
  }
}

/* Hook to keep score button state updated */
const _origPass = pass;
pass = function(){
  _origPass();
  maybeEnableScoring();
};

function resetUIState(){
  scoreBtn.disabled = true;
  scoreBtn.textContent = "計分";
  modeBadge.textContent = "對局中";
  modeBadge.classList.remove("score");
  recalcBtn.disabled = true;
  confirmBtn.disabled = true;
  warnText.textContent = "";
  renderScorePanel(null);
}

// init
resetUIState();
initState(parseInt(sizeEl.value, 10));

