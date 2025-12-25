"use strict";

const EMPTY = 0;
const BLACK = 1;
const WHITE = 2;

const boardEl = document.getElementById("board");
const sizeEl = document.getElementById("size");
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

let N = 19;
let board = [];
let turn = BLACK;
let captures = { [BLACK]: 0, [WHITE]: 0 };
let lastBoardString = "";        // ko: immediate repetition
let lastMove = null;             // {r,c}
let moveHistory = [];
let consecutivePass = 0;

// scoring mode
let scoringMode = false;
let deadMarks = new Set();       // "r,c"
let gameEnded = false;

// territory overlay in scoring mode
let territoryOwner = null;       // 2D: EMPTY/BLACK/WHITE

function opponent(color){ return color === BLACK ? WHITE : BLACK; }
function colorName(color){ return color === BLACK ? "黑" : "白"; }
function keyOf(r,c){ return `${r},${c}`; }
function parseKey(k){ const [r,c]=k.split(",").map(Number); return [r,c]; }

function initState(n){
  N = n;
  board = Array.from({ length: N }, () => Array(N).fill(EMPTY));
  turn = BLACK;
  captures = { [BLACK]: 0, [WHITE]: 0 };
  lastBoardString = boardToString(board);
  lastMove = null;
  moveHistory = [];
  consecutivePass = 0;

  scoringMode = false;
  deadMarks = new Set();
  gameEnded = false;
  territoryOwner = null;

  renderBoard();
  renderStatus();
  renderMoves();
  renderScorePanel(null);

  scoreBtn.disabled = true;
  recalcBtn.disabled = true;
  confirmBtn.disabled = true;

  hintEl.textContent = "點交叉點落子；不允許自殺；單劫禁止立刻還原上一盤面。";
}

function boardToString(b){
  return b.map(row => row.join("")).join("|");
}
function cloneBoard(b){ return b.map(row => row.slice()); }
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

function tryPlayMove(r,c){
  if(gameEnded) return { ok:false, msg:"已終局，請重置開始新局" };
  if(scoringMode) return { ok:false, msg:"目前是計分模式：請點棋子標記死子，或按『計分』退出" };

  if(!inBounds(r,c)) return { ok:false, msg:"超出棋盤" };
  if(board[r][c] !== EMPTY) return { ok:false, msg:"此處已有棋子" };

  const me = turn;
  const opp = opponent(me);

  const before = cloneBoard(board);
  const beforeCaptures = { ...captures };
  const beforeLastMove = lastMove;

  board[r][c] = me;

  let capturedCount = 0;
  for(const [nr,nc] of neighbors(r,c)){
    if(board[nr][nc] === opp){
      const g = getGroupAndLiberties(board, nr, nc);
      if(g.liberties === 0){
        capturedCount += g.stones.length;
        removeStones(board, g.stones);
      }
    }
  }

  const myGroup = getGroupAndLiberties(board, r, c);
  if(myGroup.liberties === 0){
    board = before;
    captures = beforeCaptures;
    lastMove = beforeLastMove;
    return { ok:false, msg:"不合法：自殺（禁入點）" };
  }

  const nowStr = boardToString(board);
  if(nowStr === lastBoardString){
    board = before;
    captures = beforeCaptures;
    lastMove = beforeLastMove;
    return { ok:false, msg:"不合法：劫（Ko）" };
  }

  lastBoardString = boardToString(before);

  if(capturedCount > 0) captures[me] += capturedCount;

  lastMove = { r, c };

  const coord = toCoord(r,c);
  const moveNo = moveHistory.length + 1;
  moveHistory.push(`${moveNo}. ${colorName(me)} ${coord}${capturedCount>0 ? ` x${capturedCount}` : ""}`);

  turn = opp;
  consecutivePass = 0;
  scoreBtn.disabled = true;

  return { ok:true, msg: capturedCount>0 ? `提子 ${capturedCount} 顆` : "落子成功" };
}

function toCoord(r,c){
  const letters = "ABCDEFGHJKLMNOPQRSTUVWX";
  const col = letters[c] || "?";
  const row = (N - r);
  return `${col}${row}`;
}

function pass(){
  if(gameEnded){
    hintEl.textContent = "已終局，請重置開始新局。";
    return;
  }
  if(scoringMode){
    hintEl.textContent = "計分模式中不可 Pass；請先退出計分模式。";
    return;
  }

  const me = turn;
  const moveNo = moveHistory.length + 1;
  moveHistory.push(`${moveNo}. ${colorName(me)} Pass`);
  turn = opponent(turn);
  consecutivePass += 1;

  if(consecutivePass >= 2){
    hintEl.textContent = "已連續兩次 Pass。可按『計分』進入死活標記與計分（顯示黑地/白地與輪廓）。";
    scoreBtn.disabled = false;
  }else{
    hintEl.textContent = `${colorName(me)} Pass。輪到 ${colorName(turn)}。`;
  }

  renderStatus();
  renderMoves();
}

function toggleScoringMode(){
  if(gameEnded) return;

  if(!scoringMode && consecutivePass < 2){
    hintEl.textContent = "需連續兩次 Pass 後才能計分。";
    return;
  }

  scoringMode = !scoringMode;

  if(scoringMode){
    hintEl.textContent = "計分模式：點棋子可標記死子（再點一次取消）。空地會上色顯示黑地/白地（含輪廓）。";
    modeBadge.textContent = "計分模式";
    modeBadge.classList.add("score");
    recalcBtn.disabled = false;
    confirmBtn.disabled = false;
    recalcScore();
  }else{
    hintEl.textContent = "已退出計分模式，回到對局。若要重新計分，需再次連續兩次 Pass。";
    modeBadge.textContent = "對局中";
    modeBadge.classList.remove("score");
    recalcBtn.disabled = true;
    confirmBtn.disabled = true;

    territoryOwner = null;
    renderScorePanel(null);
    renderBoard();
  }

  renderStatus();
}

function recalcScore(){
  const komi = Number(komiEl.value || 0);
  komiShowEl.textContent = String(komi);

  const score = computeScore({ komi });
  renderScorePanel(score);
  renderBoard();
}

function confirmEnd(){
  if(!scoringMode) return;
  gameEnded = true;

  hintEl.textContent = "已確認終局。若要再下一局，請按重置。";
  scoreBtn.disabled = true;
  passBtn.disabled = true;
  sizeEl.disabled = true;
  komiEl.disabled = true;

  modeBadge.textContent = "已終局";
  modeBadge.classList.add("score");

  renderStatus();
}

function reset(){
  passBtn.disabled = false;
  sizeEl.disabled = false;
  komiEl.disabled = false;
  scoreBtn.disabled = true;
  initState(parseInt(sizeEl.value, 10));
}

function renderStatus(){
  turnDot.style.background = (turn === BLACK) ? "#111" : "#f2f2f2";
  turnText.textContent = `輪到：${colorName(turn)}`;
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
    const line = moveHistory[i];
    const div = document.createElement("div");
    div.className = "m";

    const left = document.createElement("span");
    left.textContent = line;
    div.appendChild(left);

    const tag = document.createElement("span");
    tag.className = "tag";
    tag.textContent = (i === moveHistory.length - 1) ? "latest" : "";
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

/**
 * Japanese-style scoring:
 * territory + prisoners (captures + dead stones) + komi to White
 * Also computes territoryOwner for overlay (EMPTY = neutral/not-territory).
 */
function computeScore({ komi }){
  const b = cloneBoard(board);

  // remove dead stones; count as prisoners for opponent
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

  // territory calc + owner map
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

  let resultText = "";
  const diff = totalBlack - totalWhite;
  if(Math.abs(diff) < 1e-9) resultText = "平局";
  else if(diff > 0) resultText = `黑勝 +${diff.toFixed(1)}`;
  else resultText = `白勝 +${Math.abs(diff).toFixed(1)}`;

  return {
    territory,
    prisoners,
    total: { black: totalBlack, white: Number(totalWhite.toFixed(1)) },
    resultText
  };
}

function renderBoard(){
  boardEl.style.setProperty("--n", String(N));
  boardEl.innerHTML = "";

  if(scoringMode) boardEl.classList.add("score-on");
  else boardEl.classList.remove("score-on");

  const intersections = document.createElement("div");
  intersections.className = "intersections";

  for(let r=0; r<N; r++){
    for(let c=0; c<N; c++){
      const pt = document.createElement("div");
      pt.className = "pt";
      pt.dataset.r = String(r);
      pt.dataset.c = String(c);

      // ✅ territory overlay (empty points only, scoring mode only)
      if(scoringMode && territoryOwner && board[r][c] === EMPTY){
        const owner = territoryOwner[r][c]; // BLACK/WHITE/EMPTY
        const t = document.createElement("div");

        if(owner === BLACK) t.className = "territory black";
        else if(owner === WHITE) t.className = "territory white";
        else t.className = "territory neutral";

        // ✅ border outline for connected territory blocks (black/white only)
        if(owner === BLACK || owner === WHITE){
          const sameOwner = (rr, cc) => {
            if(rr < 0 || rr >= N || cc < 0 || cc >= N) return false;
            return board[rr][cc] === EMPTY && territoryOwner[rr][cc] === owner;
          };

          const topB = !sameOwner(r - 1, c);
          const rightB = !sameOwner(r, c + 1);
          const bottomB = !sameOwner(r + 1, c);
          const leftB = !sameOwner(r, c - 1);

          const W = "1.5px";
          t.style.setProperty("--bt", topB ? W : "0px");
          t.style.setProperty("--br", rightB ? W : "0px");
          t.style.setProperty("--bb", bottomB ? W : "0px");
          t.style.setProperty("--bl", leftB ? W : "0px");
        }

        pt.appendChild(t);
      }

      // hover preview only when playing
      const preview = document.createElement("div");
      preview.className = `preview ${turn === BLACK ? "black" : "white"}`;
      if(scoringMode || gameEnded) preview.style.display = "none";
      pt.appendChild(preview);

      // stones
      const v = board[r][c];
      if(v !== EMPTY){
        const stone = document.createElement("div");
        stone.className = `stone ${v === BLACK ? "black" : "white"}`;

        if(lastMove && lastMove.r === r && lastMove.c === c && !scoringMode){
          stone.classList.add("lastmove");
        }

        const dk = keyOf(r,c);
        if(scoringMode && deadMarks.has(dk)){
          stone.classList.add("dead");
        }

        pt.appendChild(stone);
      }

      pt.addEventListener("click", () => {
        const rr = parseInt(pt.dataset.r, 10);
        const cc = parseInt(pt.dataset.c, 10);

        if(scoringMode){
          if(board[rr][cc] === EMPTY){
            hintEl.textContent = "計分模式：空地只顯示地的歸屬；要改分數請標記死子（點棋子）。";
            return;
          }
          const k = keyOf(rr,cc);
          if(deadMarks.has(k)) deadMarks.delete(k);
          else deadMarks.add(k);

          recalcScore();
          return;
        }

        const res = tryPlayMove(rr, cc);
        hintEl.textContent = res.msg;
        renderBoard();
        renderStatus();
        renderMoves();
      });

      intersections.appendChild(pt);
    }
  }

  boardEl.appendChild(intersections);
}

sizeEl.addEventListener("change", reset);
passBtn.addEventListener("click", pass);
resetBtn.addEventListener("click", reset);
scoreBtn.addEventListener("click", toggleScoringMode);
recalcBtn.addEventListener("click", recalcScore);
confirmBtn.addEventListener("click", confirmEnd);

komiEl.addEventListener("input", () => {
  komiShowEl.textContent = String(Number(komiEl.value || 0));
  if(scoringMode) recalcScore();
});

// init
initState(parseInt(sizeEl.value, 10));
