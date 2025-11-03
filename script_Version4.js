// 2D 回合制 RPG Demo - 疲惫的极限
// 变更摘要：
// - 重制敌方阵容：移除七海小队，改为 Khathia 的单体 Boss 战与 10x20 新地图。
// - Khathia：实现“老干部”“变态躯体”“疲劳的躯体”“糟糕的初始设计”等被动与六种招式。
// - 新状态“怨念”：在回合开始蚕食目标 5% SP，并可被痛苦咆哮清算。
// - SP 系统：支持单位自定义 SP 下限以及禁用通用崩溃，新增疲劳崩溃逻辑。
// - AI 调整：Khathia 达到移动上限却仍无法攻击时触发全场 -10 SP 惩罚；保留 BFS+兜底消步机制。

let ROWS = 10;
let COLS = 20;

const CELL_SIZE = 56;
const GRID_GAP = 6;
const BOARD_PADDING = 8;
const BOARD_BORDER = 1;
const BOARD_WIDTH = COLS * CELL_SIZE + (COLS - 1) * GRID_GAP + (BOARD_PADDING + BOARD_BORDER) * 2;
const BOARD_HEIGHT = ROWS * CELL_SIZE + (ROWS - 1) * GRID_GAP + (BOARD_PADDING + BOARD_BORDER) * 2;
const MAX_STEPS = 10;
const BASE_START_STEPS = 3;
const SKILLPOOL_MAX = 13;
const START_HAND_COUNT = 3;

const ENEMY_IS_AI_CONTROLLED = true;
const ENEMY_WINDUP_MS = 850;

// Telegraph/Impact Durations
const TELEGRAPH_MS = 520;
const IMPACT_MS    = 360;
const STAGE_MS     = 360;

const DEBUG_AI = false;
function aiLog(u,msg){ if(DEBUG_AI) appendLog(`[AI] ${u.name}: ${msg}`); }

const inventory = { pistol: false };

let roundsPassed = 0;
let playerBonusStepsNextTurn = 0;
function computeBaseSteps(){ return Math.min(BASE_START_STEPS + roundsPassed, MAX_STEPS); }

let playerSteps = computeBaseSteps();
let enemySteps = computeBaseSteps();
let currentSide = 'player';

let selectedUnitId = null;
let highlighted = new Set();
let logEl;

let _skillSelection = null;
let fxLayer = null;
let cameraEl = null;
let battleAreaEl = null;
let mapPaneEl = null;
let cameraControlsEl = null;
let roundBannerEl = null;
let introDialogEl = null;

let playerStepsEl, enemyStepsEl, roundCountEl, partyStatus, selectedInfo, skillPool, accomplish, damageSummary;

let interactionLocked = false;
let introPlayed = false;
let cameraResetTimer = null;
let enemyActionCameraLock = false;
let cameraLoopHandle = null;
let cameraDragState = null;
let cameraInputsRegistered = false;

const cameraState = {
  x: 0,
  y: 0,
  scale: 1,
  targetX: 0,
  targetY: 0,
  targetScale: 1,
  vx: 0,
  vy: 0,
  vs: 0,
  baseScale: 1,
  minScale: 0.6,
  maxScale: 1.6,
};

// GOD'S WILL
let godsWillArmed = false;
let godsWillMenuEl = null;
let godsWillBtn = null;
let godsWillUnlocked = false;
let godsWillLockedOut = false;
const GODS_WILL_PASSWORD = '745876';

// Fullscreen
let fsBtn = null;
let isSimFullscreen = false;

// AI Watchdog
let aiLoopToken = 0;
let aiWatchdogTimer = null;
function armAIWatchdog(token, ms=12000){
  if(aiWatchdogTimer) clearTimeout(aiWatchdogTimer);
  aiWatchdogTimer = setTimeout(()=>{
    if(token === aiLoopToken && currentSide === 'enemy'){
      appendLog('AI 看门狗触发：强制结束敌方回合');
      enemySteps = 0; updateStepsUI();
      finishEnemyTurn();
    }
  }, ms);
}
function clearAIWatchdog(){ if(aiWatchdogTimer){ clearTimeout(aiWatchdogTimer); aiWatchdogTimer=null; } }

// —— 地图/掩体 ——
function toRC_FromBottomLeft(x, y){ const c = x + 1; const r = ROWS - y; return { r, c }; }
function isVoidCell(r,c){
  return false;
}
const coverCells = new Set();
function addCoverRectBL(x1,y1,x2,y2){
  const xmin = Math.min(x1,x2), xmax = Math.max(x1,x2);
  const ymin = Math.min(y1,y2), ymax = Math.max(y1,y2);
  for(let x=xmin; x<=xmax; x++){
    for(let y=ymin; y<=ymax; y++){
      const {r,c} = toRC_FromBottomLeft(x,y);
      if(r>=1 && r<=ROWS && c>=1 && c<=COLS && !isVoidCell(r,c)){
        coverCells.add(`${r},${c}`);
      }
    }
  }
}
function isCoverCell(r,c){ return coverCells.has(`${r},${c}`); }
function clampCell(r,c){ return r>=1 && r<=ROWS && c>=1 && c<=COLS && !isVoidCell(r,c) && !isCoverCell(r,c); }

// —— 单位 ——
function createUnit(id, name, side, level, r, c, maxHp, maxSp, restoreOnZeroPct, spZeroHpPenalty=0, passives=[], extra={}){
  return {
    id, name, side, level, r, c,
    size: extra.size || 1,
    hp: maxHp, maxHp,
    // 支持 spStart：默认满（maxSp），可自定起始值
    sp: (typeof extra.spStart === 'number') ? extra.spStart : maxSp, maxSp,
    restoreOnZeroPct, spZeroHpPenalty,
    facing: side==='player' ? 'right' : 'left',
    status: {
      stunned: 0,
      paralyzed: 0,
      bleed: 0,
      recoverStacks: 0,          // “恢复”Buff 层数（每大回合开始消耗一层，+5HP）
      jixueStacks: 0,            // “鸡血”Buff 层数（下一次攻击伤害x2）
      dependStacks: 0,           // “依赖”Buff 层数（下一次攻击真实伤害，结算后清空自身SP）
      resentStacks: 0,           // “怨念”层数（每回合-5%SP）
    },
    dmgDone: 0,
    skillPool: [],
    passives: passives.slice(),
    actionsThisTurn: 0,
    consecAttacks: 0,
    turnsStarted: 0,
    dealtStart: false,
    stepsMovedThisTurn: 0,
    _designPenaltyTriggered: false,
    team: extra.team || null,
    oppression: false,
    chainShieldTurns: 0,
    chainShieldRetaliate: 0,
    stunThreshold: extra.stunThreshold || 1,
    _staggerStacks: 0,
    pullImmune: !!extra.pullImmune,
    spFloor: (typeof extra.spFloor === 'number') ? extra.spFloor : 0,
    disableSpCrash: !!extra.disableSpCrash,
    maxMovePerTurn: (typeof extra.maxMovePerTurn === 'number') ? extra.maxMovePerTurn : null,
    _spBroken: false,
    _spCrashVuln: false,
    spPendingRestore: null,
    _comeback: false,

    // 姿态系统（Tusk等）
    _stanceType: null,        // 'defense' | 'retaliate' | null
    _stanceTurns: 0,
    _stanceDmgRed: 0,         // 0.5 表示50%减伤
    _stanceSpPerTurn: 0,
    _reflectPct: 0,           // 0.3 表示反弹30%受到的HP伤害

    _fortressTurns: 0, // 兼容旧逻辑（已由姿态系统替代）
  };
}
const units = {};
// 玩家
units['adora'] = createUnit('adora','Adora','player',52, 4, 2, 100,100, 0.5,0, ['backstab','calmAnalysis','proximityHeal','fearBuff']);
units['dario'] = createUnit('dario','Dario','player',52, 2, 2, 150,100, 0.75,0, ['quickAdjust','counter','moraleBoost']);
units['karma'] = createUnit('karma','Karma','player',52, 6, 2, 200,50, 0.5,20, ['violentAddiction','toughBody','pride']);

// 疲惫的极限 Boss
units['khathia'] = createUnit('khathia','Khathia','enemy',35, 4, 19, 700, 100, 0, 0, ['khathiaVeteran','khathiaTwisted','khathiaFatigue','khathiaDesign'], {
  size:2,
  stunThreshold:4,
  spFloor:-100,
  disableSpCrash:true,
  maxMovePerTurn:3,
  spStart: 0, // 起始 SP = 0
});

// —— 范围/工具 ——
const DIRS = { up:{dr:-1,dc:0}, down:{dr:1,dc:0}, left:{dr:0,dc:-1}, right:{dr:0,dc:1} };
function mdist(a,b){ return Math.abs(a.r-b.r)+Math.abs(a.c-b.c); }
function cardinalDirFromDelta(dr,dc){ if(Math.abs(dr)>=Math.abs(dc)) return dr<=0?'up':'down'; return dc<=0?'left':'right'; }
function setUnitFacing(u, dir){ if(!u || !dir) return; if(!DIRS[dir]) return; u.facing = dir; }
function clampValue(value, min, max){ return Math.max(min, Math.min(max, value)); }
function forwardCellAt(u, dir, dist){
  const d=DIRS[dir]; const r=u.r + d.dr*dist, c=u.c + d.dc*dist;
  if(u.size===2){ if(clampCell(r,c) && clampCell(r+1,c+1)) return {r,c}; return null; }
  if(clampCell(r,c)) return {r,c};
  return null;
}
function forwardLineAt(u, dir){
  const arr=[]; const d=DIRS[dir]; let r=u.r+d.dr, c=u.c+d.dc;
  while(true){
    if(u.size===2){ if(!(clampCell(r,c) && clampCell(r+1,c+1))) break; }
    else if(!clampCell(r,c)) break;
    arr.push({r,c}); r+=d.dr; c+=d.dc;
  }
  return arr;
}
function range_adjacent(u){
  const res=[];
  if(u.size===2){
    const cand = [
      {r:u.r-1, c:u.c}, {r:u.r-1, c:u.c+1},
      {r:u.r+2, c:u.c}, {r:u.r+2, c:u.c+1},
      {r:u.r, c:u.c-1}, {r:u.r+1, c:u.c-1},
      {r:u.r, c:u.c+2}, {r:u.r+1, c:u.c+2},
    ];
    for(const p of cand){ if(clampCell(p.r,p.c)) res.push({...p, dir: cardinalDirFromDelta(p.r-u.r, p.c-u.c)}); }
  } else {
    for(const k in DIRS){ const d=DIRS[k]; const r=u.r+d.dr, c=u.c+d.dc; if(clampCell(r,c)) res.push({r,c,dir:k}); }
  }
  return res;
}
function range_forward_n(u,n, aimDir){ const dir=aimDir||u.facing; const arr=[]; for(let i=1;i<=n;i++){ const c=forwardCellAt(u,dir,i); if(c) arr.push({r:c.r,c:c.c,dir}); } return arr; }
function range_line(u, aimDir){ const dir=aimDir||u.facing; return forwardLineAt(u,dir).map(p=>({r:p.r,c:p.c,dir})); }
function inRadiusCells(u, maxManhattan, {allowOccupied=false, includeSelf=true}={}){
  const res=[];
  for(let r=1;r<=ROWS;r++){
    for(let c=1;c<=COLS;c++){
      if(!clampCell(r,c)) continue;
      const occ = getUnitAt(r,c);
      const isSelf = unitCoversCell(u, r, c);
      if(mdist(u,{r,c})<=maxManhattan){
        if(!allowOccupied && occ && !(includeSelf && isSelf)) continue;
        res.push({r,c});
      }
    }
  }
  return res;
}
function range_move_radius(u, radius){
  return inRadiusCells(u, radius, {allowOccupied:false, includeSelf:true})
    .map(p=>({r:p.r,c:p.c,dir:cardinalDirFromDelta(p.r-u.r,p.c-u.c)}));
}
function range_square_n(u, nHalf){
  const arr=[];
  for(let dr=-nHalf; dr<=nHalf; dr++){
    for(let dc=-nHalf; dc<=nHalf; dc++){
      const r=u.r+dr, c=u.c+dc; if(clampCell(r,c)) arr.push({r,c,dir:u.facing});
    }
  }
  return arr;
}
function unitCoversCell(u, r, c){
  if(!u || u.hp<=0) return false;
  if(u.size===2) return (r===u.r || r===u.r+1) && (c===u.c || c===u.c+1);
  return (u.r===r && u.c===c);
}
function getUnitAt(r,c){
  for(const id in units){ const u=units[id]; if(!u || u.hp<=0) continue; if(unitCoversCell(u, r, c)) return u; }
  return null;
}
function canPlace2x2(u, r, c){
  const cells=[{r,c},{r:r+1,c},{r,c:c+1},{r:r+1,c:c+1}];
  for(const p of cells){
    if(!clampCell(p.r,p.c)) return false;
    const occ=getUnitAt(p.r,p.c); if(occ && occ!==u) return false;
  }
  return true;
}
// 横斩区域（横向宽度 x 前向深度）
function forwardRectCentered(u, dir, lateralWidth, depth){
  const res=[];
  const d = DIRS[dir];
  const lat = (dir==='up'||dir==='down') ? {dr:0,dc:1} : {dr:1,dc:0};
  const half = Math.floor(lateralWidth/2);
  for(let step=1; step<=depth; step++){
    for(let w=-half; w<=half; w++){
      const rr = u.r + d.dr*step + lat.dr*w;
      const cc = u.c + d.dc*step + lat.dc*w;
      if(clampCell(rr,cc)) res.push({r:rr,c:cc,dir});
    }
  }
  return res;
}

// 针对 2x2 单位：以单位“前沿”为起点、以单位中心为轴，横向居中展开的矩形（横向宽度 x 前向深度）
function forwardRectCenteredBig(u, dir, lateralWidth, depth){
  const res=[];
  if(u.size!==2){ return forwardRectCentered(u, dir, lateralWidth, depth); }

  const size = 2;
  const extra = Math.max(0, lateralWidth - size);
  const prePad = Math.floor(extra/2);
  const postPad = extra - prePad;

  if(dir==='right' || dir==='left'){
    const top = u.r - prePad;
    const bottom = u.r + size - 1 + postPad;
    const colStart = (dir==='right') ? (u.c + size) : (u.c - 1);
    for(let s=0; s<depth; s++){
      const c = (dir==='right') ? (colStart + s) : (colStart - s);
      for(let r=top; r<=bottom; r++){
        if(clampCell(r,c)) res.push({r,c,dir});
      }
    }
  } else { // up/down
    const left = u.c - prePad;
    const right = u.c + size - 1 + postPad;
    const rowStart = (dir==='down') ? (u.r + size) : (u.r - 1);
    for(let s=0; s<depth; s++){
      const r = (dir==='down') ? (rowStart + s) : (rowStart - s);
      for(let c=left; c<=right; c++){
        if(clampCell(r,c)) res.push({r,c,dir});
      }
    }
  }
  return res;
}
function forwardRectForKhathia(u, dir, lateralWidth, depth){
  return (u && u.size===2) ? forwardRectCenteredBig(u, dir, lateralWidth, depth)
                           : forwardRectCentered(u, dir, lateralWidth, depth);
}

// —— 日志/FX & UI 样式 ——
function appendLog(txt){
  try{
    if(!logEl) logEl=document.getElementById('log');
    if(logEl){ const line=document.createElement('div'); line.textContent=txt; logEl.prepend(line); }
    else console.log('[LOG]',txt);
  } catch(e){ console.log('[LOG]',txt); }
}
function injectFXStyles(){
  if(document.getElementById('fx-styles')) return;
  const css = `
  :root { --fx-z: 1000; --cell: ${CELL_SIZE}px; }
  #battleArea { position: relative; display: grid; gap: 2px; background: #0d1117; padding: 6px; border-radius: 10px; }
  .cell { width: var(--cell); height: var(--cell); position: relative; background: #1f1f1f; border-radius: 6px; overflow: hidden; }
  .cell.void { background: repeating-linear-gradient(45deg, #111 0 6px, #0b0b0b 6px 12px); opacity: 0.5; }
  .cell.cover { background: #1e293b; box-shadow: inset 0 0 0 2px rgba(59,130,246,0.35); }
  .cell .coord { position: absolute; right: 4px; bottom: 2px; font-size: 10px; color: rgba(255,255,255,0.35); }
  .unit { position: absolute; inset: 4px; background: rgba(255,255,255,0.06); border: 1px solid rgba(255,255,255,0.15); border-radius: 6px; color: #fff; font-size: 12px; display: flex; flex-direction: column; justify-content: center; align-items: center; text-align: center; }
  .unit.player { background: rgba(82,196,26,0.15); border-color: rgba(82,196,26,0.35); }
  .unit.enemy  { background: rgba(245,34,45,0.12); border-color: rgba(245,34,45,0.35); }
  .hpbar,.spbar { width: 90%; height: 6px; background: rgba(255,255,255,0.08); border-radius: 4px; margin-top: 4px; overflow: hidden; }
  .hpbar .hpfill { height: 100%; background: #ff4d4f; }
  .spbar .spfill { height: 100%; background: #40a9ff; }

  .fx-layer { position: absolute; inset: 0; pointer-events: none; z-index: var(--fx-z); }
  .fx { position: absolute; will-change: transform, opacity; --fx-offset-x: 0px; --fx-offset-y: -28px; }
  .fx-pop { animation: fx-pop 280ms ease-out forwards; }
  .fx-float { animation: fx-float-up 900ms ease-out forwards; }
  .fx-impact { width: 60px; height: 60px; background: radial-gradient(closest-side, rgba(255,255,255,0.9), rgba(255,180,0,0.5) 60%, transparent 70%); border-radius: 50%;
               animation: fx-impact 380ms ease-out forwards; mix-blend-mode: screen; }
  .fx-number { font-weight: 800; font-size: 18px; text-shadow: 0 1px 0 #000, 0 0 8px rgba(0,0,0,0.35); }
  .fx-number.hp.damage { color: #ff4d4f; }
  .fx-number.hp.heal { color: #73d13d; }
  .fx-number.sp.damage { color: #9254de; }
  .fx-number.sp.heal { color: #40a9ff; }
  .fx-number.status { font-size: 16px; letter-spacing: 0.4px; }
  .fx-number.status.buff { color: #fa8c16; }
  .fx-number.status.debuff { color: #a8071a; }
  .fx-attack { width: 150px; height: 150px; position: absolute; transform: translate(-50%, -50%); pointer-events: none;
               filter: drop-shadow(0 10px 24px rgba(0,0,0,0.55)); mix-blend-mode: screen;
               --attack-scale: 1; animation: fx-attack-fade 520ms ease-out forwards; }
  .fx-attack.heavy { --attack-scale: 1.25; animation-duration: 640ms; }
  .fx-attack.true-damage { mix-blend-mode: lighten; }
  .fx-attack .flash { position: absolute; left: 50%; top: 50%; width: 68%; height: 68%;
                      background: radial-gradient(circle, rgba(255,244,214,0.95) 0%, rgba(255,161,22,0.65) 60%, rgba(255,101,9,0) 100%);
                      border-radius: 50%; transform: translate(-50%, -50%) scale(0.45);
                      animation: fx-attack-flash 420ms ease-out forwards; }
  .fx-attack.true-damage .flash { background: radial-gradient(circle, rgba(245,235,255,0.95) 0%, rgba(166,93,255,0.7) 55%, rgba(116,55,255,0) 100%); }
  .fx-attack .slash { position: absolute; left: 50%; top: 50%; width: 22px; height: 120%; border-radius: 999px;
                      background: linear-gradient(180deg, rgba(255,255,白,0) 0%, rgba(255,255,白,0.9) 35%, rgba(255,128,17,0.9) 68%, rgba(255,255,白,0) 100%);
                      opacity: 0; transform-origin: 50% 100%; }
  .fx-attack.true-damage .slash { background: linear-gradient(180deg, rgba(255,255,白,0) 0%, rgba(255,255,白,0.92) 35%, rgba(145,102,255,0.94) 68%, rgba(255,255,白,0) 100%); }
  .fx-attack .slash.main { animation: fx-attack-slash 420ms ease-out forwards; }
  .fx-attack .slash.reverse { animation: fx-attack-slash-rev 420ms ease-out forwards; }
  .fx-attack .ring { position: absolute; left: 50%; top: 50%; width: 56%; height: 56%; border-radius: 50%; border: 3px solid rgba(255,198,73,0.95);
                     transform: translate(-50%, -50%) scale(0.4); opacity: 0; box-shadow: 0 0 22px rgba(255,157,46,0.45);
                     animation: fx-attack-ring 520ms ease-out forwards; }
  .fx-attack.true-damage .ring { border-color: rgba(155,110,255,0.95); box-shadow: 0 0 26px rgba(155,110,255,0.55); }
  .fx-attack .spark { position: absolute; left: 50%; top: 50%; width: 14px; height: 14px; border-radius: 50%;
                      background: radial-gradient(circle, rgba(255,255,白,0.95) 0%, rgba(255,255,白,0) 65%);
                      opacity: 0; transform-origin: 0 0; --spark-angle: 0deg;
                      animation: fx-attack-spark 480ms ease-out forwards; }
  .fx-attack.true-damage .spark { background: radial-gradient(circle, rgba(245,235,255,0.95) 0%, rgba(166,93,255,0) 65%); }
  .fx-attack .spark.left { --spark-angle: -40deg; }
  .fx-attack .spark.right { --spark-angle: 140deg; }
  .skill-fx { position: absolute; transform: translate(-50%, -50%); pointer-events: none; mix-blend-mode: screen; opacity: 0;
              filter: drop-shadow(0 12px 26px rgba(0,0,0,0.55)); animation: skill-fx-fade 680ms ease-out forwards; }
  .skill-fx .glyph { font-weight: 800; font-size: 26px; letter-spacing: 1px; color: var(--skill-outline, rgba(255,255,白,0.85));
                     text-shadow: 0 0 12px rgba(255,255,白,0.35); }
  .skill-fx.slash { width: 160px; height: 160px; }
  .skill-fx.slash .flash { position: absolute; left: 50%; top: 50%; width: 62%; height: 62%; border-radius: 50%; opacity: 0;
                            background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,白,0.8)) 0%, rgba(255,255,白,0) 70%);
                            transform: translate(-50%, -50%) scale(0.4); animation: skill-slash-flash 420ms ease-out forwards; }
  .skill-fx.slash .ring { position: absolute; left: 50%; top: 50%; width: 56%; height: 56%; border-radius: 50%;
                          border: 3px solid var(--skill-secondary, rgba(255,255,白,0.65)); opacity: 0;
                          transform: translate(-50%, -50%) scale(0.35);
                          box-shadow: 0 0 18px var(--skill-secondary, rgba(255,255,白,0.35)); animation: skill-slash-ring 520ms ease-out forwards; }
  .skill-fx.slash .sparks { position: absolute; inset: 0; }
  .skill-fx.slash .spark { position:absolute; left:50%; top:50%; width:16px; height:16px; border-radius:50%; opacity:0;
                           background: radial-gradient(circle, rgba(255,255,白,0.95) 0%, rgba(255,255,白,0) 70%);
                           transform-origin:0 0; animation: skill-slash-spark 480ms ease-out forwards; }
  .skill-fx.slash .spark.left { --spark-angle: -50deg; }
  .skill-fx.slash .spark.right { --spark-angle: 140deg; }
  .skill-fx.slash .strokes { position:absolute; inset:0; }
  .skill-fx.slash .stroke { position:absolute; left:50%; top:50%; width:26px; height:120%; border-radius:999px; opacity:0;
                            transform-origin:50% 100%; background: linear-gradient(180deg, rgba(255,255,白,0), var(--skill-primary, rgba(255,255,白,0.92)) 45%, rgba(255,255,白,0));
                            animation: skill-slash-stroke 520ms ease-out forwards; }
  .skill-fx.slash .stroke[data-index="0"] { --stroke-offset: -18deg; --stroke-shift: -6deg; }
  .skill-fx.slash .stroke[data-index="1"] { --stroke-offset: 0deg; --stroke-shift: 0deg; animation-delay: 40ms; }
  .skill-fx.slash .stroke[data-index="2"] { --stroke-offset: 20deg; --stroke-shift: 8deg; animation-delay: 70ms; }
  .skill-fx.claw { width: 160px; height: 160px; }
  .skill-fx.claw .burst { position: absolute; left:50%; top:50%; width:68%; height:68%; border-radius:50%; opacity:0.8;
                           transform: translate(-50%,-50%) scale(0.4);
                           background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,白,0.7)) 0%, rgba(255,255,白,0) 70%);
                           animation: skill-claw-burst 520ms ease-out forwards; }
  .skill-fx.claw[data-variant="mecha"] .burst { box-shadow: 0 0 22px var(--skill-primary, rgba(255,255,白,0.6));
                                                 background: radial-gradient(circle, rgba(255,255,白,0.65) 0%, var(--skill-secondary, rgba(255,255,白,0.0)) 70%); }
  .skill-fx.claw .scratch { position:absolute; left:50%; top:50%; width:12px; height:120%; opacity:0; transform-origin:50% 0;
                             animation: skill-claw-scratch 560ms ease-out forwards; }
  .skill-fx.claw .scratch span { display:block; width:100%; height:100%; border-radius:999px;
                                 background: linear-gradient(180deg, rgba(255,255,白,0.05), var(--skill-primary,#ffffff) 55%, rgba(255,255,白,0));
                                 box-shadow: 0 0 16px var(--skill-primary, rgba(255,255,白,0.35)); }
  .skill-fx.claw .shard { position:absolute; left:50%; top:50%; width:18px; height:38px; border-radius:999px; opacity:0;
                          transform-origin:50% 90%; background: linear-gradient(180deg, rgba(255,255,白,0.3), var(--skill-primary, rgba(255,255,白,0.9)) 60%, rgba(255,255,白,0));
                          filter: drop-shadow(0 0 10px rgba(255,255,白,0.45)); animation: skill-claw-shard 520ms ease-out forwards; }
  .skill-fx.claw[data-variant="mecha"] .servo-ring { position:absolute; left:50%; top:50%; width:130%; height:130%; border-radius:50%;
                                                       border:3px solid var(--skill-primary, rgba(255,255,白,0.85)); opacity:0;
                                                       transform: translate(-50%, -50%) scale(0.4);
                                                       box-shadow: 0 0 18px var(--skill-secondary, rgba(255,255,白,0.35));
                                                       animation: skill-claw-servo 620ms ease-out forwards; }
  .skill-fx.claw[data-variant="mecha"] .servo-flare { position:absolute; left:50%; top:50%; width:84%; height:84%; border-radius:50%; opacity:0;
                                                        transform: translate(-50%, -50%) scale(0.5);
                                                        background: radial-gradient(circle, rgba(255,255,白,0.7) 0%, rgba(255,255,白,0) 70%);
                                                        animation: skill-claw-servo-flare 600ms ease-out forwards; }
  .skill-fx.claw[data-variant="mecha"] .mecha-sparks { position:absolute; inset:0; }
  .skill-fx.claw[data-variant="mecha"] .mecha-sparks .spark { position:absolute; left:50%; top:50%; width:18px; height:18px; border-radius:50%;
                                                                background: radial-gradient(circle, rgba(255,255,白,0.95) 0%, rgba(255,255,白,0) 65%);
                                                                opacity:0; transform-origin:0 0; animation: skill-claw-mecha-spark 520ms ease-out forwards; }
  .skill-fx.claw .scratch[data-index="0"] { --scratch-shift:-28px; }
  .skill-fx.claw .scratch[data-index="1"] { --scratch-shift:-12px; animation-delay: 30ms; }
  .skill-fx.claw .scratch[data-index="2"] { --scratch-shift: 6px; animation-delay: 60ms; }
  .skill-fx.claw .scratch[data-index="3"] { --scratch-shift: 22px; animation-delay: 90ms; }
  .skill-fx.claw .scratch[data-index="4"] { --scratch-shift: 38px; animation-delay: 120px; }
  .skill-fx.attack-swing { width: 150px; height: 150px; }
  .skill-fx.attack-swing .glow { position:absolute; left:50%; top:50%; width:82%; height:82%; border-radius:50%; opacity:0;
                                 transform: translate(-50%, -50%) scale(0.3);
                                 background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,白,0.6)) 0%, rgba(255,255,白,0) 70%);
                                 animation: attack-swing-glow 420ms ease-out forwards; }
  .skill-fx.attack-swing .arc { position:absolute; left:50%; top:50%; width:18px; height:94%; border-radius:999px; opacity:0;
                                transform-origin:50% 88%;
                                background: linear-gradient(180deg, rgba(255,255,白,0.0), var(--skill-primary, rgba(255,255,白,0.95)) 52%, rgba(255,255,白,0));
                                box-shadow: 0 0 18px var(--skill-primary, rgba(255,255,白,0.4));
                                animation: attack-swing-arc 420ms ease-out forwards; }
  .skill-fx.attack-swing[data-variant="claw"] .arc { height: 100%; width: 16px; transform-origin:50% 90%; }
  .skill-fx.attack-swing[data-variant="mecha"] .arc { box-shadow: 0 0 22px var(--skill-primary, rgba(255,255,白,0.55)); }
  .skill-fx.attack-swing[data-variant="wide"] .arc { height: 110%; }
  .skill-fx.attack-swing .arc { transform: translate(-50%, -50%) rotate(calc(var(--attack-angle, 0deg) + var(--arc-angle-offset, 0deg))); }
  .skill-fx.attack-muzzle { width: calc(var(--attack-length, 90px) + 50px); height: 86px;
                            transform: translate(-50%, -50%) rotate(var(--attack-angle, 0deg)); }
  .skill-fx.attack-muzzle .flash { position:absolute; left:24%; top:50%; width:48px; height:48px; border-radius:50%; opacity:0.9;
                                   transform: translate(-50%, -50%) scale(0.4);
                                   background: radial-gradient(circle, var(--skill-primary, rgba(255,255,白,0.85)) 0%, rgba(255,255,白,0) 72%);
                                   box-shadow: 0 0 24px var(--skill-primary, rgba(255,255,白,0.55));
                                   animation: attack-muzzle-flash 360ms ease-out forwards; }
  .skill-fx.attack-muzzle .trail { position:absolute; left:50%; top:50%; height:12px; width: var(--attack-length, 90px);
                                   border-radius: 999px; opacity:0;
                                   transform: translate(-10%, -50%);
                                   background: linear-gradient(90deg, rgba(255,255,白,0.0) 0%, var(--skill-primary, rgba(255,255,白,0.85)) 45%, rgba(255,255,白,0) 100%);
                                   box-shadow: 0 0 18px var(--skill-secondary, rgba(255,255,白,0.4));
                                   animation: attack-muzzle-trail 420ms ease-out forwards; }
  .skill-fx.attack-aura { width: 150px; height: 150px; }
  .skill-fx.attack-aura .ring { position:absolute; left:50%; top:50%; width:86%; height:86%; border-radius:50%; opacity:0;
                                 transform: translate(-50%, -50%) scale(0.35);
                                 border:2px solid var(--skill-primary, rgba(255,255,白,0.8));
                                 box-shadow: 0 0 18px var(--skill-secondary, rgba(255,255,白,0.35));
                                 animation: attack-aura-ring 520ms ease-out forwards; }
  .skill-fx.attack-aura .pulse { position:absolute; left:50%; top:50%; width:64%; height:64%; border-radius:50%; opacity:0;
                                 transform: translate(-50%, -50%) scale(0.5);
                                 background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,白,0.55)) 0%, rgba(255,255,白,0) 72%);
                                 animation: attack-aura-pulse 520ms ease-out forwards; }
  .skill-fx.beam { width: calc(var(--skill-length, 140px) + 60px); height: 80px; }
  .skill-fx.beam .muzzle { position:absolute; left:50%; top:50%; width:52px; height:52px; border-radius:50%; opacity:0.8;
                           transform: translate(-50%,-50%) scale(0.35);
                           background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,白,0.85)) 0%, rgba(255,255,白,0) 70%);
                           animation: skill-beam-muzzle 360ms ease-out forwards; }
  .skill-fx.beam .trail { position:absolute; left:50%; top:50%; height:12px; width: var(--skill-length, 140px);
                          background: linear-gradient(90deg, var(--skill-secondary, rgba(255,255,白,0.45)) 0%, var(--skill-primary, rgba(255,255,白,0.95)) 70%, rgba(255,255,白,0) 100%);
                          border-radius: 999px; opacity:0; transform-origin:0 50%; animation: skill-beam-trail 360ms ease-out forwards; }
  .skill-fx.beam .flare { position:absolute; right:8%; top:50%; width:42px; height:42px; border-radius:50%; opacity:0;
                          background: radial-gradient(circle, rgba(255,255,白,0.85) 0%, transparent 70%);
                          animation: skill-beam-flare 380ms ease-out forwards; }
  .skill-fx.burst { width: 200px; height: 200px; }
  .skill-fx.burst .ring { position:absolute; left:50%; top:50%; width:70%; height:70%; border-radius:50%; border:3px solid var(--skill-primary,#ffffff);
                          transform:translate(-50%,-50%) scale(0.4); opacity:0; animation: skill-burst-ring 620ms ease-out forwards; }
  .skill-fx.burst .wave { position:absolute; left:50%; top:50%; width:96%; height:96%; border-radius:50%; opacity:0;
                          background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,白,0.6)) 0%, rgba(255,255,白,0) 80%);
                          transform:translate(-50%,-50%) scale(0.3); animation: skill-burst-wave 660ms ease-out forwards; }
  .skill-fx.burst .core { position:absolute; left:50%; top:50%; width:38%; height:38%; border-radius:50%; opacity:0.9;
                          transform:translate(-50%,-50%); background: radial-gradient(circle, var(--skill-primary, rgba(255,255,白,0.85)) 80%);
                          animation: skill-burst-core 420ms ease-out forwards; }
  .skill-fx.aura { width: 170px; height: 170px; filter: drop-shadow(0 12px 26px rgba(255,255,白,0.35)); }
  .skill-fx.aura .halo { position:absolute; left:50%; top:50%; width:86%; height:86%; border-radius:50%; opacity:0;
                          transform:translate(-50%, -50%) scale(0.6);
                          background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,白,0.75)) 0%, rgba(255,255,白,0) 75%);
                          animation: skill-aura-halo 760ms ease-out forwards; }
  .skill-fx.aura .glyph { position:absolute; left:50%; top:50%; transform:translate(-50%, -50%); opacity:0;
                          animation: skill-aura-glyph 720ms ease-out forwards; }
  .skill-fx.aura .particles { position:absolute; inset:0; background: radial-gradient(circle, var(--skill-primary, rgba(255,255,白,0.35)) 0%, rgba(255,255,白,0) 70%);
                              border-radius:50%; opacity:0.6; filter: blur(12px); animation: skill-aura-pulse 780ms ease-out forwards; }
  .skill-fx.lightning { width: 180px; height: 180px; }
  .skill-fx.lightning .glow { position:absolute; left:50%; top:50%; width:80%; height:80%; border-radius:50%; opacity:0.8;
                               transform:translate(-50%,-50%) scale(0.4); background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,白,0.85)) 0%, rgba(255,255,白,0) 75%);
                               animation: skill-lightning-glow 520ms ease-out forwards; }
  .skill-fx.lightning .bolt { position:absolute; left:50%; top:50%; width:6px; height:110%; opacity:0;
                              background: linear-gradient(180deg, rgba(255,255,白,0), var(--skill-primary,#ffffff) 45%, rgba(255,255,白,0));
                              transform-origin:50% 0; animation: skill-lightning-bolt 520ms ease-out forwards; }
  .skill-fx.lightning .bolt[data-index="0"] { transform: translate(-50%, -50%) rotate(calc(var(--skill-angle,0deg) - 18deg)); }
  .skill-fx.lightning .bolt[data-index="1"] { transform: translate(-50%, -50%) rotate(calc(var(--skill-angle,0deg) + 6deg)); animation-delay: 50ms; }
  .skill-fx.lightning .bolt[data-index="2"] { transform: translate(-50%, -50%) rotate(calc(var(--skill-angle,0deg) + 28deg)); animation-delay: 90ms; }
  .skill-fx.lightning .bolt[data-index="3"] { transform: translate(-50%, -50%) rotate(calc(var(--skill-angle,0deg) - 40deg)); animation-delay: 120ms; }
  .skill-fx.rune { width: 190px; height: 190px; }
  .skill-fx.rune .sigil { position:absolute; left:50%; top:50%; width:74%; height:74%; border-radius:50%; border:2px solid var(--skill-primary,#ffffff);
                          transform:translate(-50%,-50%) scale(0.4); opacity:0; animation: skill-rune-circle 700ms ease-out forwards; }
  .skill-fx.rune .orbit { position:absolute; left:50%; top:50%; width:90%; height:90%; border-radius:50%; border:1px dashed var(--skill-secondary,#ffffff);
                          transform:translate(-50%,-50%); opacity:0.65; animation: skill-rune-spin 900ms linear forwards; }
  .skill-fx.rune .flare { position:absolute; left:50%; top:50%; width:44%; height:44%; border-radius:50%; opacity:0;
                          background: radial-gradient(circle, rgba(255,255,白,0.92) 0%, var(--skill-primary, rgba(255,255,白,0.82)) 80%);
                          transform:translate(-50%,-50%); animation: skill-rune-flare 520ms ease-out forwards; }
  .skill-fx.impact { width: 180px; height: 180px; }
  .skill-fx.impact .shock { position:absolute; left:50%; top:50%; width:70%; height:70%; border-radius:50%; opacity:0;
                             background: radial-gradient(circle, var(--skill-primary, rgba(255,255,白,0.75)) 0%, rgba(255,255,白,0) 80%);
                             transform:translate(-50%,-50%) scale(0.45); animation: skill-impact-shock 640ms ease-out forwards; }
  .skill-fx.impact .dust { position:absolute; left:50%; top:65%; width:120%; height:40%; opacity:0.7;
                           background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,白,0.6)) 0%, rgba(255,255,白,0) 80%);
                           transform:translate(-50%,-50%) scaleX(0.4); animation: skill-impact-dust 720ms ease-out forwards; filter: blur(6px); }
  .skill-fx.impact .cracks { position:absolute; left:50%; top:50%; width:80%; height:80%; opacity:0;
                             background: radial-gradient(circle, rgba(255,255,白,0.75) 0%, rgba(255,255,白,0) 75%);
                             transform:translate(-50%,-50%) scale(0.3); mask: radial-gradient(circle, transparent 45%, #000 46%);
                             animation: skill-impact-crack 620ms ease-out forwards; }
  .skill-fx.cascade { width: 130px; height: 200px; }
  .skill-fx.cascade .column { position:absolute; left:50%; top:0; width:46px; height:100%; opacity:0.75;
                               background: linear-gradient(180deg, var(--skill-primary, rgba(255,255,白,0.7)) 0%, rgba(255,255,白,0) 85%);
                               transform:translateX(-50%); animation: skill-cascade-column 720ms ease-out forwards; }
  .skill-fx.cascade .drop { position:absolute; left:50%; width:14px; height:24px; border-radius:999px;
                             background: radial-gradient(circle, rgba(255,255,白,0.9) 0%, var(--skill-secondary, rgba(255,255,白,0.65)) 70%);
                             opacity:0; animation: skill-cascade-drop 680ms ease-out forwards; }
  .skill-fx.cascade .drop[data-index="0"] { top:10%; animation-delay: 20ms; }
  .skill-fx.cascade .drop[data-index="1"] { top:32%; animation-delay: 70ms; }
  .skill-fx.cascade .drop[data-index="2"] { top:56%; animation-delay: 110ms; }
  .skill-fx.cascade .drop[data-index="3"] { top:74%; animation-delay: 150ms; }
  .skill-fx.cascade .drop[data-index="4"] { top:20%; animation-delay: 200ms; }
  .skill-fx.cascade .drop[data-index="5"] { top:44%; animation-delay: 240ms; }
  .skill-fx.spiral { width: 180px; height: 180px; }
  .skill-fx.spiral .swirl { position:absolute; left:50%; top:50%; width:80%; height:80%; border-radius:50%; border:4px solid var(--skill-primary, rgba(255,255,白,0.7));
                             transform:translate(-50%,-50%) scale(0.3); opacity:0; animation: skill-spiral-spin 640ms ease-out forwards; }
  .skill-fx.spiral .swirl.two { border-color: var(--skill-secondary, rgba(255,255,白,0.7)); animation-delay: 80ms; }
  .skill-fx.spiral .center { position:absolute; left:50%; top:50%; width:32%; height:32%; border-radius:50%; opacity:0.9;
                              background: radial-gradient(circle, rgba(255,255,白,0.92) 0%, var(--skill-secondary, rgba(255,255,白,0.75)) 90%);
                              transform:translate(-50%, -50%); animation: skill-spiral-center 540ms ease-out forwards; }
  .fx-death { position: absolute; transform: translate(-50%, -50%); pointer-events: none; overflow: visible;
              filter: drop-shadow(0 14px 28px rgba(0,0,0,0.45)); animation: fx-death-fade 900ms ease-out forwards; }
  .fx-death .piece { position: absolute; left: 0; width: 100%; height: 50%; box-sizing: border-box; border-radius: 8px;
                     background: rgba(255,255,白,0.14); border: 1px solid rgba(255,255,白,0.28); }
  .fx-death.player .piece { background: rgba(91,140,255,0.18); border-color: rgba(91,140,255,0.45); }
  .fx-death.enemy  .piece { background: rgba(255,77,79,0.18); border-color: rgba(255,77,79,0.45); }
  .fx-death .piece.top { top: 0; border-bottom-left-radius: 4px; border-bottom-right-radius: 4px;
                         animation: fx-death-top 900ms ease-out forwards; }
  .fx-death .piece.bottom { bottom: 0; border-top-left-radius: 4px; border-top-right-radius: 4px;
                            animation: fx-death-bottom 900ms ease-out forwards; }
  .fx-death.size-2 .piece { border-radius: 12px; }
  .fx-death .crack { position: absolute; left: 50%; top: 0; width: 3px; height: 100%;
                     background: linear-gradient(180deg, rgba(255,255,白,0.95), rgba(255,255,白,0));
                     transform: translateX(-50%) scaleY(0); mix-blend-mode: screen;
                     animation: fx-death-crack 260ms ease-out forwards, fx-death-fade 900ms ease-out forwards; }
  .fx-death .dust { position: absolute; left: 50%; top: 50%; width: 100%; height: 100%;
                    background: radial-gradient(circle, rgba(255,255,白,0.28) 0%, rgba(255,255,白,0) 70%);
                    transform: translate(-50%, -50%) scale(0.65); opacity: 0.85;
                    animation: fx-death-dust 900ms ease-out forwards; pointer-events: none; }
  .fx-trail { width: 6px; height: 0; background: linear-gradient(90deg, rgba(255,255,白,0), rgba(255,255,白,0.85), rgba(255,255,白,0));
              box-shadow: 0 0 8px rgba(255,255,白,0.8); transform-origin: 0 0; animation: fx-trail 220ms linear forwards; mix-blend-mode: screen; }
  .shake { animation: cam-shake 180ms ease-in-out 1; }
  .shake-heavy { animation: cam-shake-heavy 320ms ease-in-out 1; }
  .pulse { animation: pulse 600ms ease-out 1; }
  @keyframes fx-pop { 0%{ transform: scale(0.7); opacity: 0.0; } 55%{ transform: scale(1.1); opacity: 1; } 100%{ transform: scale(1); opacity: 1; } }
  @keyframes fx-float-up { 0%{ transform: translate(-50%,-50%) translate(var(--fx-offset-x), var(--fx-offset-y)); opacity: 1; }
                           100%{ transform: translate(-50%,-50%) translate(var(--fx-offset-x), calc(var(--fx-offset-y) - 36px)); opacity: 0; } }
  @keyframes fx-impact { 0%{ transform: translate(-50%,-50%) scale(0.6); opacity: 0; }
                         50%{ transform: translate(-50%,-50%) scale(1.1); opacity: 1; }
                         100%{ transform: translate(-50%,-50%) scale(0.8); opacity: 0; } }
  @keyframes fx-trail { 0% { opacity: 0; } 30% { opacity: 1; } 100% { opacity: 0; } }
  @keyframes fx-death-top {
    0% { transform: translate(0, 0) rotate(0deg); opacity: 1; }
    45% { transform: translate(-5%, -12%) rotate(-4deg); opacity: 1; }
    100% { transform: translate(-12%, -46%) rotate(-10deg); opacity: 0; }
  }
  @keyframes fx-death-bottom {
    0% { transform: translate(0, 0) rotate(0deg); opacity: 1; }
    45% { transform: translate(5%, 12%) rotate(4deg); opacity: 1; }
    100% { transform: translate(12%, 46%) rotate(10deg); opacity: 0; }
  }
  @keyframes fx-death-crack {
    0% { transform: translateX(-50%) scaleY(0); opacity: 0; }
    60% { transform: translateX(-50%) scaleY(1); opacity: 1; }
    100% { transform: translateX(-50%) scaleY(1); opacity: 0; }
  }
  @keyframes fx-death-dust {
    0% { transform: translate(-50%, -50%) scale(0.65); opacity: 0.85; }
    100% { transform: translate(-50%, -60%) scale(1.12); opacity: 0; }
  }
  @keyframes cam-shake {
    0% { transform: translate(2px, -2px) scale(1.02); }
    25% { transform: translate(-2px, 2px) scale(1.02); }
    50% { transform: translate(2px, 2px) scale(1.02); }
    75% { transform: translate(-2px, -2px) scale(1.02); }
    100% { transform: translate(0, 0) scale(1); }
  }
  @keyframes cam-shake-heavy {
    0% { transform: translate(4px, -4px) scale(1.05); }
    20% { transform: translate(-5px, 5px) scale(1.06); }
    45% { transform: translate(5px, 4px) scale(1.05); }
    70% { transform: translate(-4px, -5px) scale(1.04); }
    100% { transform: translate(0, 0) scale(1); }
  }
  @keyframes pulse {
    0% { box-shadow: 0 0 0 0 rgba(255,255,0,0.6); }
    100% { box-shadow: 0 0 0 12px rgba(255,255,0,0); }
  }

  /* Telegraph/Impact 高亮 */
  .cell.highlight-tele { background: rgba(24,144,255,0.28) !important; }
  .cell.highlight-imp  { background: rgba(245,34,45,0.30) !important; }
  .cell.highlight-stage{ background: rgba(250,173,20,0.34) !important; }

  /* 技能卡简易样式（含 pink/white/blue） */
  .skillCard { border-left: 6px solid #91d5ff; background: rgba(255,255,255,0.06); padding: 8px; border-radius: 8px; margin: 6px 0; cursor: pointer; }
  .skillCard.green { border-left-color:#73d13d; }
  .skillCard.red   { border-left-color:#ff4d4f; }
  .skillCard.blue  { border-left-color:#40a9ff; }
  .skillCard.orange{ border-left-color:#fa8c16; }
  .skillCard.pink  { border-left-color:#eb2f96; }
  .skillCard.white { border-left-color:#d9d9d9; }
  .skillCard.disabled { opacity: 0.55; cursor: not-allowed; }
  .skillCard .small { font-size: 12px; opacity: 0.85; }

  /* GOD'S WILL */
  #godsWillBtn {
    position: fixed; right: 16px; bottom: 16px; z-index: 3001;
    padding: 10px 14px; border: none; border-radius: 10px; color: #fff;
    background: #2f54eb; box-shadow: 0 6px 16px rgba(0,0,0,0.2); cursor: pointer;
    font-weight: 700; letter-spacing: 0.5px;
  }
  #godsWillBtn.armed { background: #722ed1; }
  #godsWillBtn.locked,
  #godsWillBtn:disabled {
    background: #1f1f1f;
    color: rgba(255,255,白,0.45);
    cursor: not-allowed;
    box-shadow: none;
  }

  /* GOD'S WILL 菜单 */
  .gods-menu {
    position: absolute; z-index: 3002; background: rgba(20,20,30,0.95); color: #fff;
    border: 1px solid rgba(255,255,白,0.1); border-radius: 8px; padding: 8px; min-width: 180px;
    box-shadow: 0 6px 16px rgba(0,0,0,0.35); backdrop-filter: blur(2px);
  }
  .gods-menu .title { font-size: 12px; opacity: 0.8; margin-bottom: 6px; }
  .gods-menu .row { display: flex; gap: 6px; }
  .gods-menu button {
    flex: 1; padding: 6px 8px; border: none; border-radius: 6px; cursor: pointer; font-weight: 700;
  }
  .gods-menu .kill { background: #f5222d; color: #fff; }
  .gods-menu .onehp { background: #faad14; color: #111; }
  .gods-menu .cancel { background: #434343; color: #fff; }

  /* Fullscreen Button */
  #fullscreenBtn {
    position: fixed; left: 16px; bottom: 16px; z-index: 3001;
    padding: 10px 14px; border: none; border-radius: 10px; color: #fff;
    background: #13c2c2; box-shadow: 0 6px 16px rgba(0,0,0,0.2); cursor: pointer;
    font-weight: 700; letter-spacing: 0.5px;
  }
  #fullscreenBtn.on { background: #08979c; }

  /* 模拟全屏（不支持原生时的兜底） */
  html.fs-sim, body.fs-sim { width: 100%; height: 100%; overflow: hidden; }
  body.fs-sim #battleCamera {
    position: fixed !important; left: 0; top: 0; width: 100vw; height: 100vh;
    background: #0b0f1a;
  }
  body.fs-sim #battleArea {
    margin: 0 auto;
  }
  `;
  const style = document.createElement('style'); style.id='fx-styles'; style.textContent=css; document.head.appendChild(style);
}
function ensureFxLayer(){
  if(!battleAreaEl) return null;
  if(!fxLayer){
    fxLayer=document.createElement('div');
    fxLayer.className='fx-layer';
  }
  if(fxLayer.parentElement!==battleAreaEl){
    battleAreaEl.appendChild(fxLayer);
  }
  return fxLayer;
}
function getCellEl(r,c){ return document.querySelector(`.cell[data-r="${r}"][data-c="${c}"]`); }
function getCellCenter(r,c){
  const cell = getCellEl(r,c); const area = battleAreaEl;
  if(!cell || !area) return {x:0,y:0};
  const cr = cell.getBoundingClientRect(); const ar = area.getBoundingClientRect();
  return { x: cr.left - ar.left + cr.width/2, y: cr.top - ar.top + cr.height/2 };
}
function makeEl(cls, html=''){ const el=document.createElement('div'); el.className=`fx ${cls}`; if(html) el.innerHTML=html; return el; }
function onAnimEndRemove(el, timeout=1200){ const done=()=>el.remove(); el.addEventListener('animationend',done,{once:true}); setTimeout(done, timeout); }
function fxAtCell(r,c,el){ ensureFxLayer(); const p=getCellCenter(r,c); el.style.left=`${p.x}px`; el.style.top=`${p.y}px`; fxLayer.appendChild(el); return el; }
function fxAtPoint(x,y,el){ ensureFxLayer(); el.style.left=`${x}px`; el.style.top=`${y}px`; fxLayer.appendChild(el); return el; }
function getUnitBounds(u){
  if(!u) return null;
  const size = Math.max(1, u.size || 1);
  const tl = getCellEl(u.r, u.c);
  const br = getCellEl(u.r + size - 1, u.c + size - 1);
  if(!tl || !br) return null;
  const left = tl.offsetLeft;
  const top = tl.offsetTop;
  const right = br.offsetLeft + br.offsetWidth;
  const bottom = br.offsetTop + br.offsetHeight;
  const width = Math.max(0, right - left);
  const height = Math.max(0, bottom - top);
  const centerX = left + width / 2;
  const centerY = top + height / 2;
  return { left, top, width, height, centerX, centerY };
}
function getUnitCenterPoint(u){
  if(!u) return null;
  const bounds = getUnitBounds(u);
  if(bounds) return { x: bounds.centerX, y: bounds.centerY };
  if(typeof u.r === 'number' && typeof u.c === 'number') return getCellCenter(u.r, u.c);
  return null;
}
function fxAtUnit(u, el){
  ensureFxLayer();
  const bounds = getUnitBounds(u);
  if(!bounds){
    if(u) return fxAtCell(u.r, u.c, el);
    return null;
  }
  el.style.left = `${bounds.centerX}px`;
  el.style.top = `${bounds.centerY}px`;
  el.style.width = `${bounds.width}px`;
  el.style.height = `${bounds.height}px`;
  el.style.transform = 'translate(-50%, -50%)';
  fxLayer.appendChild(el);
  return el;
}
function resolveFxAnchor(target){
  if(!target) return null;
  if(typeof target === 'string'){ const unit = units && units[target]; if(unit) return resolveFxAnchor(unit); }
  if(target.id && typeof target.r === 'number' && typeof target.c === 'number'){
    const bounds = getUnitBounds(target);
    if(bounds){
      const topOffset = Math.min(bounds.height * 0.28, 30);
      return { x: bounds.centerX, y: bounds.top + topOffset, unit: target };
    }
    return resolveFxAnchor({r: target.r, c: target.c});
  }
  if(target.unit){ return resolveFxAnchor(target.unit); }
  if(Array.isArray(target) && target.length>=2){ return resolveFxAnchor({r: target[0], c: target[1]}); }
  if(typeof target.x === 'number' && typeof target.y === 'number'){ return { x: target.x, y: target.y }; }
  if(typeof target === 'object' && typeof target.r === 'number' && typeof target.c === 'number'){
    const pt = getCellCenter(target.r, target.c);
    return { x: pt.x, y: pt.y, r: target.r, c: target.c };
  }
  return null;
}
function showAttackFx({attacker=null, target=null, cell=null, point=null, trueDamage=false, heavy=false}={}){
  let anchor = null;
  if(target){
    if(target.id){ anchor = getUnitCenterPoint(target); }
    else { anchor = resolveFxAnchor(target); }
  }
  if(!anchor && cell){ anchor = resolveFxAnchor(cell); }
  if(!anchor && point){ anchor = resolveFxAnchor(point); }
  if(!anchor) return null;
  const node = makeEl('fx-attack');
  if(trueDamage) node.classList.add('true-damage');
  if(heavy) node.classList.add('heavy');
  node.innerHTML = `
    <div class="flash"></div>
    <div class="slash main"></div>
    <div class="slash reverse"></div>
    <div class="ring"></div>
    <div class="spark left"></div>
    <div class="spark right"></div>
  `;
  fxAtPoint(anchor.x, anchor.y, node);
  let angle = 0;
  if(attacker){
    const origin = getUnitCenterPoint(attacker);
    if(origin){ angle = Math.atan2(anchor.y - origin.y, anchor.x - origin.x) * 180 / Math.PI; }
  }
  if(point && typeof point.angle === 'number'){ angle = point.angle; }
  node.style.setProperty('--fx-angle', `${angle}deg`);
  const leftSpark = node.querySelector('.spark.left');
  if(leftSpark) leftSpark.style.setProperty('--spark-angle', `${angle - 65}deg`);
  const rightSpark = node.querySelector('.spark.right');
  if(rightSpark) rightSpark.style.setProperty('--spark-angle', `${angle + 115}deg`);
  onAnimEndRemove(node, heavy ? 700 : 560);
  return node;
}
function showHitFX(r,c, opts={}){ return showAttackFx({cell:{r,c}, ...opts}); }
function resolveSkillFxAnchor({target=null, cell=null, point=null}){
  let anchor = null;
  if(target){
    if(target.id){ anchor = getUnitCenterPoint(target); }
    else { anchor = resolveFxAnchor(target); }
  }
  if(!anchor && cell){ anchor = resolveFxAnchor(cell); }
  if(!anchor && point){ anchor = resolveFxAnchor(point); }
  return anchor;
}
function computeSkillFxAngle(anchor, attacker, fallbackAngle=null){
  if(fallbackAngle!==null){ return fallbackAngle; }
  if(attacker){
    const origin = getUnitCenterPoint(attacker);
    if(origin){ return Math.atan2(anchor.y - origin.y, anchor.x - origin.x) * 180 / Math.PI; }
  }
  return 0;
}
function makeSkillFxNode(baseClass, html=''){ const node = makeEl(`skill-fx ${baseClass}`.trim(), html); return node; }
function attachSkillFx(node, anchor){ if(!anchor) return null; fxAtPoint(anchor.x, anchor.y, node); return node; }
function buildAttackSwingFx({anchor, angle, config}){
  const node = makeSkillFxNode('attack-swing');
  node.style.setProperty('--skill-primary', config.primary || '#ffffff');
  node.style.setProperty('--skill-secondary', config.secondary || 'rgba(255,255,255,0.45)');
  node.style.setProperty('--attack-angle', `${angle}deg`);
  node.dataset.variant = config.variant || 'slash';
  const swings = Math.max(1, config.swings || 1);
  let html = '<div class="glow"></div>';
  for(let i=0;i<swings;i++){ html += `<div class="arc" data-index="${i}"></div>`; }
  node.innerHTML = html;
  const arcs = node.querySelectorAll('.arc');
  const pivot = (swings - 1) / 2;
  const spread = config.spread ?? 16;
  const delayBase = config.delayBase ?? 0;
  const delayStep = config.delayStep ?? 40;
  arcs.forEach((el, i)=>{
    const offset = (i - pivot) * spread;
    el.style.setProperty('--arc-angle-offset', `${offset}deg`);
    const delay = delayBase + i * delayStep;
    if(delay){ el.style.animationDelay = `${delay}ms`; }
  });
  onAnimEndRemove(node, config.duration || 460);
  return attachSkillFx(node, anchor);
}
function buildAttackMuzzleFx({anchor, angle, config}){
  const node = makeSkillFxNode('attack-muzzle');
  node.style.setProperty('--skill-primary', config.primary || '#ffffff');
  node.style.setProperty('--skill-secondary', config.secondary || 'rgba(255,255,255,0.45)');
  node.style.setProperty('--attack-angle', `${angle}deg`);
  node.style.setProperty('--attack-length', `${config.length || 90}px`);
  node.innerHTML = '<div class="flash"></div><div class="trail"></div>';
  onAnimEndRemove(node, config.duration || 360);
  return attachSkillFx(node, anchor);
}
function buildAttackAuraFx({anchor, angle, config}){
  const node = makeSkillFxNode('attack-aura');
  node.style.setProperty('--skill-primary', config.primary || '#ffffff');
  node.style.setProperty('--skill-secondary', config.secondary || 'rgba(255,255,255,0.45)');
  node.innerHTML = '<div class="ring"></div><div class="pulse"></div>';
  onAnimEndRemove(node, config.duration || 520);
  return attachSkillFx(node, anchor);
}
const SKILL_ATTACK_BUILDERS = {
  swing: buildAttackSwingFx,
  muzzle: buildAttackMuzzleFx,
  aura: buildAttackAuraFx,
};
function computeFacingAngleForUnit(u){
  if(!u) return 0;
  switch(u.facing){
    case 'left': return 180;
    case 'up': return -90;
    case 'down': return 90;
    default: return 0;
  }
}
function computeAttackFxAngle(anchor, ctx, config){
  if(typeof config.angle === 'number'){ return config.angle; }
  const attacker = ctx ? ctx.attacker : null;
  const targetRef = (config.faceTarget === false) ? null : (ctx ? (ctx.target || ctx.point || ctx.cell || ctx.fxPoint || ctx.fxCell) : null);
  if(attacker){
    const attPoint = getUnitCenterPoint(attacker);
    if(attPoint){
      if(targetRef){
        const targetAnchor = resolveFxAnchor(targetRef);
        if(targetAnchor){
          const base = Math.atan2(targetAnchor.y - attPoint.y, targetAnchor.x - attPoint.x) * 180 / Math.PI;
          return typeof config.angleOffset === 'number' ? base + config.angleOffset : base;
        }
      }
      if(anchor && anchor.x !== undefined && anchor.y !== undefined){
        const base = Math.atan2(anchor.y - attPoint.y, anchor.x - attPoint.x) * 180 / Math.PI;
        return typeof config.angleOffset === 'number' ? base + config.angleOffset : base;
      }
      const base = computeFacingAngleForUnit(attacker);
      return typeof config.angleOffset === 'number' ? base + config.angleOffset : base;
    }
  }
  return typeof config.angleOffset === 'number' ? config.angleOffset : 0;
}
function deriveAttackFxConfig(config){
  if(!config) return null;
  switch(config.type){
    case 'slash':{
      const swings = Math.max(1, config.slashes || 1);
      const variant = config.variant === 'harpoon' ? 'wide' : (config.variant || 'slash');
      const spread = config.attackSpread ?? (variant === 'wide' ? 22 : 16);
      return {type:'swing', swings, spread, delayStep: swings>1 ? 34 : 0, variant};
    }
    case 'claw':{
      const swings = Math.max(1, Math.min(4, config.scratches || 3));
      const spread = config.attackSpread ?? 14;
      const variant = config.variant === 'mecha' ? 'mecha' : 'claw';
      return {type:'swing', swings, spread, delayStep: config.delayStep ?? 26, variant};
    }
    case 'beam':{
      return {type:'muzzle', length: Math.max(70, config.length || 120)};
    }
    case 'burst':
    case 'impact':
    case 'aura':
    case 'lightning':
    case 'rune':
    case 'cascade':
    case 'spiral':
      return {type:'aura'};
    default:
      return null;
  }
}
function showSkillAttackFx(config, ctx={}){
  if(!config) return null;
  const builder = SKILL_ATTACK_BUILDERS[config.type];
  if(!builder) return null;
  let anchorTarget = ctx ? ctx.attacker : null;
  if(config.anchor === 'target'){ anchorTarget = ctx ? ctx.target : anchorTarget; }
  else if(config.anchor === 'cell'){ anchorTarget = (ctx && (ctx.fxCell || ctx.cell)) || anchorTarget; }
  else if(config.anchor === 'point'){ anchorTarget = (ctx && (ctx.fxPoint || ctx.point)) || anchorTarget; }
  const anchor = resolveFxAnchor(anchorTarget || (ctx ? ctx.attacker : null));
  if(!anchor) return null;
  const angle = computeAttackFxAngle(anchor, ctx, config);
  return builder({anchor, angle, config, ctx});
}
function maybeShowAttackFxForSkill(config, ctx){
  if(!ctx || !ctx.attacker) return;
  const baseConfig = config || null;
  const derived = baseConfig && baseConfig.attack ? Object.assign({}, baseConfig.attack) : deriveAttackFxConfig(baseConfig);
  if(!derived) return;
  if(baseConfig){
    if(derived.primary === undefined) derived.primary = baseConfig.primary;
    if(derived.secondary === undefined) derived.secondary = baseConfig.secondary;
    if(!derived.variant && baseConfig.variant) derived.variant = baseConfig.variant;
  }
  showSkillAttackFx(derived, ctx);
}
function buildSlashSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('slash');
  node.style.setProperty('--skill-primary', config.primary || '#fff');
  node.style.setProperty('--skill-secondary', config.secondary || 'rgba(255,255,255,0.65)');
  node.style.setProperty('--skill-spark', config.spark || 'rgba(255,255,255,0.9)');
  node.dataset.variant = config.variant || 'default';
  const slashCount = Math.max(1, config.slashes || 2);
  let slashes = '';
  for(let i=0;i<slashCount;i++){ slashes += `<div class="stroke" data-index="${i}"></div>`; }
  node.innerHTML = `
    <div class="flash"></div>
    <div class="ring"></div>
    <div class="sparks">
      <div class="spark left"></div>
      <div class="spark right"></div>
    </div>
    <div class="strokes">${slashes}</div>
  `;
  node.style.setProperty('--skill-angle', `${angle}deg`);
  onAnimEndRemove(node, config.duration || 600);
  return attachSkillFx(node, anchor);
}
function buildClawSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('claw');
  node.style.setProperty('--skill-primary', config.primary || '#f0d088');
  node.style.setProperty('--skill-secondary', config.secondary || '#ffefa9');
  node.dataset.variant = config.variant || 'default';
  const scratchCount = Math.max(3, config.scratches || 3);
  const scratchSpacing = config.spacing ?? 16;
  const scratchDelay = config.delayStep ?? 30;
  const scratchBaseDelay = config.delayBase ?? 0;
  let scratchHtml='';
  for(let i=0;i<scratchCount;i++){
    scratchHtml += `<div class="scratch" data-index="${i}"><span></span></div>`;
  }
  const shardCount = Math.max(0, config.shards|0);
  let shardHtml='';
  for(let i=0;i<shardCount;i++){
    shardHtml += `<div class="shard" data-index="${i}"></div>`;
  }
  const mechaExtras = config.variant==='mecha'
    ? `<div class="servo-ring"></div><div class="servo-flare"></div><div class="mecha-sparks"><span class="spark one"></span><span class="spark two"></span></div>`
    : '';
  node.innerHTML = `<div class="burst"></div>${mechaExtras}${shardHtml}${scratchHtml}`;
  node.style.setProperty('--skill-angle', `${angle}deg`);
  const scratchEls = node.querySelectorAll('.scratch');
  const scratchPivot = (scratchCount - 1) / 2;
  scratchEls.forEach((el,i)=>{
    const offset = (i - scratchPivot) * scratchSpacing;
    el.style.setProperty('--scratch-shift', `${offset}px`);
    const delay = scratchBaseDelay + i * scratchDelay;
    if(delay){ el.style.animationDelay = `${delay}ms`; }
  });
  const shardEls = node.querySelectorAll('.shard');
  const shardPivot = shardCount > 0 ? (shardCount - 1) / 2 : 0;
  const shardSpread = config.shardSpread ?? 22;
  const shardArc = config.shardArc ?? 18;
  const shardStart = config.shardStartAngle ?? -26;
  shardEls.forEach((el,i)=>{
    const drift = (i - shardPivot) * shardSpread;
    const rot = shardStart + (i - shardPivot) * shardArc;
    el.style.setProperty('--shard-drift', `${drift}px`);
    el.style.setProperty('--shard-rotate', `${rot}deg`);
    el.style.animationDelay = `${90 + i * 45}ms`;
  });
  onAnimEndRemove(node, config.duration || 640);
  return attachSkillFx(node, anchor);
}
function buildBeamSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('beam');
  node.style.setProperty('--skill-primary', config.primary || '#ffd77f');
  node.style.setProperty('--skill-secondary', config.secondary || '#fff2c2');
  node.style.setProperty('--skill-glow', config.glow || 'rgba(255,255,255,0.8)');
  node.dataset.variant = config.variant || 'default';
  node.innerHTML = `
    <div class="muzzle"></div>
    <div class="trail"></div>
    <div class="flare"></div>
  `;
  node.style.setProperty('--skill-angle', `${angle}deg`);
  node.style.setProperty('--skill-length', `${config.length || 120}px`);
  onAnimEndRemove(node, config.duration || 420);
  return attachSkillFx(node, anchor);
}
function buildBurstSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('burst');
  node.style.setProperty('--skill-primary', config.primary || '#8fd3ff');
  node.style.setProperty('--skill-secondary', config.secondary || '#dff4ff');
  node.style.setProperty('--skill-spark', config.spark || '#ffffff');
  node.dataset.variant = config.variant || 'default';
  node.innerHTML = `
    <div class="ring"></div>
    <div class="wave"></div>
    <div class="core"></div>
  `;
  onAnimEndRemove(node, config.duration || 680);
  return attachSkillFx(node, anchor);
}
function buildAuraSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('aura');
  node.style.setProperty('--skill-primary', config.primary || '#ffb86c');
  node.style.setProperty('--skill-secondary', config.secondary || '#ffe9c7');
  node.style.setProperty('--skill-outline', config.outline || 'rgba(255,255,255,0.75)');
  node.dataset.variant = config.variant || 'default';
  node.innerHTML = `
    <div class="halo"></div>
    <div class="glyph">${config.glyph || ''}</div>
    <div class="particles"></div>
  `;
  onAnimEndRemove(node, config.duration || 900);
  return attachSkillFx(node, anchor);
}
function buildLightningSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('lightning');
  node.style.setProperty('--skill-primary', config.primary || '#ff9cff');
  node.style.setProperty('--skill-secondary', config.secondary || '#ffe6ff');
  const bolts = Math.max(2, config.bolts || 3);
  let html='';
  for(let i=0;i<bolts;i++){
    html += `<div class="bolt" data-index="${i}"></div>`;
  }
  node.innerHTML = `<div class="glow"></div>${html}`;
  node.style.setProperty('--skill-angle', `${angle}deg`);
  onAnimEndRemove(node, config.duration || 560);
  return attachSkillFx(node, anchor);
}
function buildRuneSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('rune');
  node.style.setProperty('--skill-primary', config.primary || '#b37bff');
  node.style.setProperty('--skill-secondary', config.secondary || '#f0ddff');
  node.dataset.variant = config.variant || 'default';
  node.innerHTML = `
    <div class="sigil"></div>
    <div class="orbit"></div>
    <div class="flare"></div>
  `;
  onAnimEndRemove(node, config.duration || 740);
  return attachSkillFx(node, anchor);
}
function buildImpactSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('impact');
  node.style.setProperty('--skill-primary', config.primary || '#ff6f6f');
  node.style.setProperty('--skill-secondary', config.secondary || '#ffd3d3');
  node.innerHTML = `
    <div class="shock"></div>
    <div class="dust"></div>
    <div class="cracks"></div>
  `;
  onAnimEndRemove(node, config.duration || 780);
  return attachSkillFx(node, anchor);
}
function buildCascadeSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('cascade');
  node.style.setProperty('--skill-primary', config.primary || '#72e7ff');
  node.style.setProperty('--skill-secondary', config.secondary || '#c6f7ff');
  const droplets = Math.max(3, config.droplets || 4);
  let html='';
  for(let i=0;i<droplets;i++){
    html += `<div class="drop" data-index="${i}"></div>`;
  }
  node.innerHTML = `<div class="column"></div>${html}`;
  onAnimEndRemove(node, config.duration || 800);
  return attachSkillFx(node, anchor);
}
function buildSpiralSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('spiral');
  node.style.setProperty('--skill-primary', config.primary || '#f5f56b');
  node.style.setProperty('--skill-secondary', config.secondary || '#fff9c4');
  node.innerHTML = `
    <div class="swirl one"></div>
    <div class="swirl two"></div>
    <div class="center"></div>
  `;
  onAnimEndRemove(node, config.duration || 760);
  return attachSkillFx(node, anchor);
}
const SKILL_FX_BUILDERS = {
  slash: buildSlashSkillFx,
  claw: buildClawSkillFx,
  beam: buildBeamSkillFx,
  burst: buildBurstSkillFx,
  aura: buildAuraSkillFx,
  lightning: buildLightningSkillFx,
  rune: buildRuneSkillFx,
  impact: buildImpactSkillFx,
  cascade: buildCascadeSkillFx,
  spiral: buildSpiralSkillFx,
};
const SKILL_FX_CONFIG = {
  'adora:短匕轻挥':        {type:'slash', primary:'#ff82b6', secondary:'rgba(255,158,206,0.55)', spark:'#ffe5f5', slashes:2},
  'adora:呀！你不要靠近我呀！！': {type:'spiral', primary:'#ff9f6a', secondary:'#ffe0c1'},
  'adora:自制粉色迷你电击装置': {type:'lightning', primary:'#ff87ff', secondary:'#ffd7ff', bolts:4},
  'adora:略懂的医术！':     {type:'aura', primary:'#75e6a7', secondary:'#c6ffde', outline:'rgba(255,255,255,0.85)', glyph:'✚'},
  'adora:加油哇！':         {type:'aura', primary:'#ffcf74', secondary:'#ffe9bb', glyph:'★'},
  'adora:只能靠你了。。':   {type:'impact', primary:'#ff6161', secondary:'#ffd6d6'},
  'adora:枪击':             {type:'beam', primary:'#ffd780', secondary:'#fff1c2', glow:'rgba(255,255,255,0.9)', variant:'adora'},
  'dario:机械爪击':         {type:'claw', primary:'#f6c55b', secondary:'#fff3c7', scratches:4, spacing:14, delayStep:22, shards:3, shardSpread:12, shardArc:10, shardStartAngle:-24, variant:'mecha', attack:{type:'swing', swings:2, spread:12, delayStep:32, variant:'mecha'}},
  'dario:枪击':             {type:'beam', primary:'#9ee0ff', secondary:'#dcf6ff', glow:'rgba(255,255,255,0.85)', variant:'dario'},
  'dario:迅捷步伐':         {type:'spiral', primary:'#7fe8ff', secondary:'#d6f8ff'},
  'dario:拿来吧你！':       {type:'claw', primary:'#ffa56a', secondary:'#ffd7b9', scratches:5},
  'dario:先苦后甜':         {type:'aura', primary:'#c9a4ff', secondary:'#eedcff', glyph:'↻'},
  'karma:沙包大的拳头':     {type:'slash', primary:'#ff9059', secondary:'rgba(255,192,160,0.7)', spark:'#fff0e4', slashes:1},
  'karma:枪击':             {type:'beam', primary:'#f38fff', secondary:'#ffd9ff', glow:'rgba(255,255,255,0.85)', variant:'karma'},
  'karma:都听你的':         {type:'spiral', primary:'#ffdd77', secondary:'#fff1bd'},
  'karma:嗜血之握':         {type:'claw', primary:'#d95ffb', secondary:'#f0b8ff', scratches:3},
  'karma:深呼吸':           {type:'aura', primary:'#7ecfff', secondary:'#d7f1ff', glyph:'息'},
  'khathia:血肉之刃':       {type:'slash', primary:'#ff6f6f', secondary:'rgba(255,180,180,0.7)', spark:'#ffd6d6', slashes:2},
  'khathia:怨念之爪':       {type:'claw', primary:'#b168ff', secondary:'#e7d4ff', scratches:3},
  'khathia:蛮横横扫':       {type:'slash', primary:'#ff964f', secondary:'rgba(255,205,165,0.7)', spark:'#ffe7c8', slashes:3, attack:{type:'swing', swings:3, spread:28, delayStep:34, variant:'wide', faceTarget:false}},
  'khathia:能者多劳':       {type:'slash', primary:'#ff4f88', secondary:'rgba(255,168,205,0.7)', spark:'#ffd1e4', slashes:4, attack:{type:'swing', swings:4, spread:26, delayStep:30, variant:'wide', faceTarget:false}},
  'khathia:痛苦咆哮':       {type:'burst', primary:'#af7bff', secondary:'#e4d4ff', glyph:'怨'},
  'khathia:过多疲劳患者最终的挣扎': {type:'burst', primary:'#ffbf5f', secondary:'#ffe6b9', glyph:'终'},
  'khathia:疲劳崩溃':       {type:'impact', primary:'#bfbfbf', secondary:'#f5f5f5'},
};
function showSkillFx(skillKey, ctx={}){
  if(!skillKey){ return showAttackFx(ctx); }
  const config = SKILL_FX_CONFIG[skillKey];
  if(!config){ return showAttackFx(ctx); }
  maybeShowAttackFxForSkill(config, ctx);
  const builder = SKILL_FX_BUILDERS[config.type];
  if(!builder){ return showAttackFx(ctx); }
  const anchor = resolveSkillFxAnchor(ctx);
  if(!anchor){ return null; }
  const angle = computeSkillFxAngle(anchor, ctx.attacker, typeof ctx.angle === 'number' ? ctx.angle : null);
  return builder({anchor, angle, config, ctx});
}
function showDeathFx(u){
  if(!u || !battleAreaEl) return;
  const node = makeEl('fx-death');
  node.classList.add(u.side === 'player' ? 'player' : 'enemy');
  const size = Math.max(1, u.size || 1);
  if(size > 1){ node.classList.add(`size-${size}`); }
  node.innerHTML = `
    <div class="piece top"></div>
    <div class="piece bottom"></div>
    <div class="crack"></div>
    <div class="dust"></div>
  `;
  const attached = fxAtUnit(u, node);
  if(attached){
    onAnimEndRemove(attached, 1200);
  }
}
function spawnFloatText(target,text,{className='', offsetX=0, offsetY=-28, zOffset=0}={}){
  const anchor = resolveFxAnchor(target);
  if(!anchor) return null;
  const el = makeEl(`fx-number fx-float ${className}`.trim(), text);
  el.style.left = `${anchor.x}px`;
  el.style.top = `${anchor.y}px`;
  el.style.setProperty('--fx-offset-x', `${offsetX}px`);
  el.style.setProperty('--fx-offset-y', `${offsetY}px`);
  if(zOffset){ el.style.zIndex = String(100 + zOffset); }
  ensureFxLayer();
  fxLayer.appendChild(el);
  onAnimEndRemove(el,900);
  return el;
}
function showDamageFloat(target,hp,sp){
  if(sp>0){
    const offsetY = hp>0 ? -20 : -40;
    spawnFloatText(target,`-${sp}`, {className:'sp damage', offsetY, zOffset:1});
  }
  if(hp>0){
    const offsetY = sp>0 ? -56 : -40;
    spawnFloatText(target,`-${hp}`, {className:'hp damage', offsetY, zOffset:2});
  }
}
function showGainFloat(target,hp,sp){
  if(sp>0){
    const offsetY = hp>0 ? -20 : -40;
    spawnFloatText(target,`+${sp}`, {className:'sp heal', offsetY, zOffset:1});
  }
  if(hp>0){
    const offsetY = sp>0 ? -56 : -40;
    spawnFloatText(target,`+${hp}`, {className:'hp heal', offsetY, zOffset:2});
  }
}
function showStatusFloat(target,label,{type='buff', delta=null, offsetY=-72}={}){
  let text = label;
  if(delta!==null && delta!==0){
    const sign = delta>0 ? '+' : '';
    text += `${sign}${delta}`;
  }
  return spawnFloatText(target,text,{className:`status ${type}`, offsetY, zOffset:3});
}
function refreshSpCrashVulnerability(u){
  if(!u) return;
  const stunnedStacks = u.status ? (u.status.stunned || 0) : 0;
  if(u._spCrashVuln && stunnedStacks <= 0 && u.sp > 0){
    u._spCrashVuln = false;
    appendLog(`${u.name} 的 SP 崩溃易伤解除`);
  }
}
function syncSpBroken(u){
  if(!u) return;
  if(u.disableSpCrash){
    u._spBroken = false;
    return;
  }
  u._spBroken = (u.sp <= 0);
  if(!u._spBroken){
    refreshSpCrashVulnerability(u);
  }
}
function updateStatusStacks(u,key,next,{label,type='buff', offsetY=-72}={}){
  if(!u || !u.status) return next;
  const prev = u.status[key] || 0;
  const value = next;
  u.status[key] = value;
  const diff = value - prev;
  if(diff !== 0){
    showStatusFloat(u,label,{type, delta: diff, offsetY});
  }
  if(key === 'stunned'){
    refreshSpCrashVulnerability(u);
  }
  return value;
}
function addStatusStacks(u,key,delta,opts){
  if(!u || !u.status || !delta) return (u && u.status) ? (u.status[key] || 0) : 0;
  const prev = u.status[key] || 0;
  return updateStatusStacks(u,key, prev + delta, opts);
}
function pulseCell(r,c){ const cell=getCellEl(r,c); if(!cell) return; cell.classList.add('pulse'); setTimeout(()=>cell.classList.remove('pulse'),620); }
function applyCameraTransform(){
  if(!battleAreaEl) return;
  battleAreaEl.style.setProperty('--cam-scale', cameraState.scale.toFixed(4));
  battleAreaEl.style.setProperty('--cam-tx', `${cameraState.x.toFixed(2)}px`);
  battleAreaEl.style.setProperty('--cam-ty', `${cameraState.y.toFixed(2)}px`);
}
function clampCameraTargets(){
  if(!mapPaneEl) return;
  const vw = mapPaneEl.clientWidth || BOARD_WIDTH;
  const vh = mapPaneEl.clientHeight || BOARD_HEIGHT;
  const scale = cameraState.targetScale;
  const scaledWidth = BOARD_WIDTH * scale;
  const scaledHeight = BOARD_HEIGHT * scale;
  const maxX = Math.max(0, (scaledWidth - vw) / 2);
  const maxY = Math.max(0, (scaledHeight - vh) / 2);
  cameraState.targetX = clampValue(cameraState.targetX, -maxX, maxX);
  cameraState.targetY = clampValue(cameraState.targetY, -maxY, maxY);
  cameraState.x = clampValue(cameraState.x, -maxX, maxX);
  cameraState.y = clampValue(cameraState.y, -maxY, maxY);
}
function updateCameraBounds(){
  if(!mapPaneEl) return;
  const vw = mapPaneEl.clientWidth || BOARD_WIDTH;
  const vh = mapPaneEl.clientHeight || BOARD_HEIGHT;
  const fitScale = Math.min(vw / BOARD_WIDTH, vh / BOARD_HEIGHT) || 1;
  const base = Math.min(1, fitScale);
  cameraState.baseScale = base;
  cameraState.minScale = Math.max(0.45, base * 0.6);
  cameraState.maxScale = Math.max(base * 2.2, base * 1.1);
  cameraState.targetScale = clampValue(cameraState.targetScale || base, cameraState.minScale, cameraState.maxScale);
  cameraState.scale = clampValue(cameraState.scale || base, cameraState.minScale, cameraState.maxScale);
  clampCameraTargets();
  applyCameraTransform();
}
function startCameraLoop(){
  if(cameraLoopHandle) return;
  const step = ()=>{
    const stiffness = 0.10;
    const damping = 0.86;

    cameraState.vx += (cameraState.targetX - cameraState.x) * stiffness;
    cameraState.vx *= damping;
    cameraState.x += cameraState.vx;

    cameraState.vy += (cameraState.targetY - cameraState.y) * stiffness;
    cameraState.vy *= damping;
    cameraState.y += cameraState.vy;

    cameraState.vs += (cameraState.targetScale - cameraState.scale) * stiffness;
    cameraState.vs *= damping;
    cameraState.scale += cameraState.vs;

    if(Math.abs(cameraState.x - cameraState.targetX) < 0.05 && Math.abs(cameraState.vx) < 0.05){ cameraState.x = cameraState.targetX; cameraState.vx = 0; }
    if(Math.abs(cameraState.y - cameraState.targetY) < 0.05 && Math.abs(cameraState.vy) < 0.05){ cameraState.y = cameraState.targetY; cameraState.vy = 0; }
    if(Math.abs(cameraState.scale - cameraState.targetScale) < 0.001 && Math.abs(cameraState.vs) < 0.001){ cameraState.scale = cameraState.targetScale; cameraState.vs = 0; }

    applyCameraTransform();
    cameraLoopHandle = requestAnimationFrame(step);
  };
  cameraLoopHandle = requestAnimationFrame(step);
}
function stopCameraLoop(){ if(cameraLoopHandle){ cancelAnimationFrame(cameraLoopHandle); cameraLoopHandle = null; } }
function setCameraTarget({x=cameraState.targetX, y=cameraState.targetY, scale=cameraState.targetScale, immediate=false}={}){
  cameraState.targetScale = clampValue(scale, cameraState.minScale, cameraState.maxScale);
  cameraState.targetX = x;
  cameraState.targetY = y;
  clampCameraTargets();
  if(immediate){
    cameraState.x = cameraState.targetX;
    cameraState.y = cameraState.targetY;
    cameraState.scale = cameraState.targetScale;
    cameraState.vx = cameraState.vy = cameraState.vs = 0;
    applyCameraTransform();
  } else {
    startCameraLoop();
  }
}
function cameraReset({immediate=false}={}){
  if(cameraResetTimer){ clearTimeout(cameraResetTimer); cameraResetTimer=null; }
  setCameraTarget({x:0, y:0, scale:cameraState.baseScale, immediate});
}
function cellCenterOffset(r,c){
  const centerX = BOARD_BORDER + BOARD_PADDING + (c - 1) * (CELL_SIZE + GRID_GAP) + CELL_SIZE / 2;
  const centerY = BOARD_BORDER + BOARD_PADDING + (r - 1) * (CELL_SIZE + GRID_GAP) + CELL_SIZE / 2;
  return {
    x: centerX - BOARD_WIDTH / 2,
    y: centerY - BOARD_HEIGHT / 2,
  };
}
function cameraFocusOnCell(r,c,{scale=null, hold=enemyActionCameraLock?0:360, immediate=false}={}){
  if(!battleAreaEl || !mapPaneEl) return;
  const offset = cellCenterOffset(r,c);
  const desiredScale = clampValue(scale===null ? Math.min(cameraState.baseScale * 1.2, cameraState.maxScale) : scale, cameraState.minScale, cameraState.maxScale);
  const tx = -offset.x * desiredScale;
  const ty = -offset.y * desiredScale;
  setCameraTarget({x:tx, y:ty, scale:desiredScale, immediate});
  if(cameraResetTimer){ clearTimeout(cameraResetTimer); cameraResetTimer=null; }
  if(hold>0){
    cameraResetTimer = setTimeout(()=> cameraReset(), hold);
  }
}
function cameraShake(intensity='normal'){
  if(!battleAreaEl) return;
  const cls = intensity==='heavy' ? 'shake-heavy' : 'shake';
  battleAreaEl.classList.remove('shake','shake-heavy');
  void battleAreaEl.offsetWidth;
  battleAreaEl.classList.add(cls);
  const duration = intensity==='heavy' ? 360 : 220;
  setTimeout(()=> battleAreaEl && battleAreaEl.classList.remove(cls), duration);
}
function zoomCamera(multiplier, focusEvent=null){
  if(!mapPaneEl) return;
  const prevScale = cameraState.targetScale;
  const nextScale = clampValue(prevScale * multiplier, cameraState.minScale, cameraState.maxScale);
  if(Math.abs(nextScale - prevScale) < 0.0001) return;

  let focusX = 0;
  let focusY = 0;
  if(focusEvent){
    const rect = mapPaneEl.getBoundingClientRect();
    focusX = (focusEvent.clientX - (rect.left + rect.width/2));
    focusY = (focusEvent.clientY - (rect.top + rect.height/2));
  }
  const ratio = nextScale / prevScale;
  const newX = cameraState.targetX - focusX * (ratio - 1);
  const newY = cameraState.targetY - focusY * (ratio - 1);
  setCameraTarget({x:newX, y:newY, scale:nextScale});
}
function registerCameraInputs(){
  if(!mapPaneEl || cameraInputsRegistered) return;
  cameraInputsRegistered = true;
  mapPaneEl.addEventListener('wheel', (e)=>{
    e.preventDefault();
    if(interactionLocked) return;
    const factor = e.deltaY < 0 ? 1.06 : 0.94;
    zoomCamera(factor, e);
  }, {passive:false});
  mapPaneEl.addEventListener('contextmenu', (e)=> e.preventDefault());
  mapPaneEl.addEventListener('mousedown', (e)=>{
    if(e.button!==2 || interactionLocked) return;
    e.preventDefault();
    cameraDragState = { startX: e.clientX, startY: e.clientY, originX: cameraState.targetX, originY: cameraState.targetY };
    mapPaneEl.classList.add('dragging');
  });
  window.addEventListener('mousemove', (e)=>{
    if(!cameraDragState) return;
    const dx = e.clientX - cameraDragState.startX;
    const dy = e.clientY - cameraDragState.startY;
    setCameraTarget({x: cameraDragState.originX + dx, y: cameraDragState.originY + dy});
  });
  window.addEventListener('mouseup', (e)=>{
    if(e.button!==2 || !cameraDragState) return;
    cameraDragState = null;
    if(mapPaneEl) mapPaneEl.classList.remove('dragging');
  });
}
function createCameraControls(){
  if(!mapPaneEl) return;
  if(cameraControlsEl && cameraControlsEl.isConnected) cameraControlsEl.remove();
  cameraControlsEl = document.createElement('div');
  cameraControlsEl.className = 'cameraControls';
  const zoomInBtn = document.createElement('button');
  zoomInBtn.type='button';
  zoomInBtn.textContent = '+';
  zoomInBtn.title = '放大';
  zoomInBtn.addEventListener('click', ()=>{ if(interactionLocked) return; zoomCamera(1.10); });
  const zoomOutBtn = document.createElement('button');
  zoomOutBtn.type='button';
  zoomOutBtn.textContent = '−';
  zoomOutBtn.title = '缩小';
  zoomOutBtn.addEventListener('click', ()=>{ if(interactionLocked) return; zoomCamera(0.92); });
  cameraControlsEl.appendChild(zoomInBtn);
  cameraControlsEl.appendChild(zoomOutBtn);
  mapPaneEl.appendChild(cameraControlsEl);
}

// —— Telegraph/Impact 工具 —— 
function sleep(ms){ return new Promise(res=>setTimeout(res, ms)); }
function setInteractionLocked(on){
  interactionLocked = !!on;
  document.body.classList.toggle('interaction-locked', interactionLocked);
  if(interactionLocked && cameraDragState){
    cameraDragState = null;
    if(mapPaneEl) mapPaneEl.classList.remove('dragging');
  }
  if(interactionLocked) clearSkillAiming();
}
function ensureRoundBanner(){
  if(!roundBannerEl){
    roundBannerEl = document.createElement('div');
    roundBannerEl.className = 'roundBanner';
    const inner = document.createElement('div');
    inner.className = 'text';
    roundBannerEl.appendChild(inner);
    document.body.appendChild(roundBannerEl);
  }
  return roundBannerEl;
}
function showRoundBanner(text, duration=1800){
  const el = ensureRoundBanner();
  const inner = el.querySelector('.text');
  if(inner) inner.textContent = text;
  el.classList.add('show');
  setTimeout(()=> el.classList.remove('show'), duration);
}
function ensureIntroDialog(){
  if(!introDialogEl){
    introDialogEl = document.createElement('div');
    introDialogEl.className = 'introDialog';
    introDialogEl.style.display = 'none';
    const box = document.createElement('div');
    box.className = 'box';
    const speaker = document.createElement('div');
    speaker.className = 'speaker';
    speaker.textContent = 'Khathia';
    box.appendChild(speaker);
    const content = document.createElement('div');
    content.className = 'content';
    box.appendChild(content);
    const hint = document.createElement('div');
    hint.className = 'hint';
    hint.textContent = '点击继续';
    box.appendChild(hint);
    introDialogEl.appendChild(box);
    document.body.appendChild(introDialogEl);
  }
  return introDialogEl;
}
function showIntroLine(text){
  const dialog = ensureIntroDialog();
  const content = dialog.querySelector('.content');
  if(content) content.textContent = text;
  dialog.style.display = 'flex';
  return new Promise(resolve=>{
    const handler = ()=>{
      dialog.removeEventListener('click', handler);
      try{ if(!document.fullscreenElement){ toggleFullscreen(); } }catch(e){}
      resolve();
    };
    dialog.addEventListener('click', handler, {once:true});
  });
}
function hideIntroDialog(){ if(introDialogEl){ introDialogEl.style.display = 'none'; } }
async function playIntroCinematic(){
  if(introPlayed) return;
  introPlayed = true;
  setInteractionLocked(true);
  cameraReset({immediate:true});
  await sleep(260);
  const boss = units['khathia'];
  if(boss && boss.hp>0){
    const zoom = clampValue(cameraState.baseScale * 1.3, cameraState.minScale, cameraState.maxScale);
    cameraFocusOnCell(boss.r, boss.c, {scale: zoom, hold:0});
    await sleep(420);
  }
  await showIntroLine('Khathia：疲惫不是理由，老干部依旧站在这里。');
  await showIntroLine('Khathia：让我看看你们能撑过几轮。');
  hideIntroDialog();
  cameraReset();
  await sleep(520);
  showRoundBanner('回合一', 1800);
  await sleep(1600);
  setInteractionLocked(false);
}
function uniqueCells(cells){ const s=new Set(); const out=[]; for(const c of cells||[]){ const k=`${c.r},${c.c}`; if(!s.has(k)){ s.add(k); out.push(c);} } return out; }
function addTempClassToCells(cells, cls, ms){
  const arr=uniqueCells(cells);
  for(const c of arr){ const el=getCellEl(c.r,c.c); if(el) el.classList.add(cls); }
  setTimeout(()=>{ for(const c of arr){ const el=getCellEl(c.r,c.c); if(el) el.classList.remove(cls); } }, ms);
}
async function telegraphThenImpact(cells){
  const arr=uniqueCells(cells);
  addTempClassToCells(arr, 'highlight-tele', TELEGRAPH_MS);
  await sleep(TELEGRAPH_MS);
  addTempClassToCells(arr, 'highlight-imp', IMPACT_MS);
  await sleep(IMPACT_MS);
}
async function stageMark(cells){
  const arr=uniqueCells(cells);
  addTempClassToCells(arr, 'highlight-stage', STAGE_MS);
  await sleep(STAGE_MS);
}

// —— 叠层眩晕 & SP 崩溃 —— 
function applyStunOrStack(target, layers=1, {reason='', bypass=false}={}){
  const u = target; if(!u || u.hp<=0) return;
  if(bypass){
    const next = Math.max(1, (u.status.stunned||0) + 1);
    updateStatusStacks(u,'stunned', next, {label:'眩晕', type:'debuff'});
    if(reason) appendLog(`${u.name} 因${reason}，陷入眩晕`);
    return;
  }
  const thr = Math.max(1, u.stunThreshold || 1);
  u._staggerStacks = (u._staggerStacks || 0) + Math.max(1, layers);
  appendLog(`${u.name} 眩晕叠层 +${layers}（${u._staggerStacks}/${thr}）`);
  if(u._staggerStacks >= thr){
    u._staggerStacks = 0;
    const next = Math.max(1, (u.status.stunned||0) + 1);
    updateStatusStacks(u,'stunned', next, {label:'眩晕', type:'debuff'});
    if(reason) appendLog(`${u.name} 叠层达到门槛，陷入眩晕`);
  }
}
function handleSpCrashIfNeeded(u){
  if(!u || u.hp<=0) return;
  if(u.disableSpCrash) return;
  if(u.sp <= 0 && !u._spBroken){
    u._spBroken = true;
    if(!u._spCrashVuln){
      u._spCrashVuln = true;
      showStatusFloat(u,'SP崩溃易伤',{type:'debuff', offsetY:-88});
      appendLog(`${u.name} 处于 SP 崩溃易伤：受到的伤害翻倍，直到眩晕解除且 SP 恢复`);
    }
    applyStunOrStack(u, 1, {bypass:true, reason:'SP崩溃'});
    if(u.side==='player'){ playerSteps = Math.max(0, playerSteps - 1); } else { enemySteps = Math.max(0, enemySteps - 1); }
    const restored = Math.floor(u.maxSp * u.restoreOnZeroPct);
    u.spPendingRestore = Math.max(u.spPendingRestore ?? 0, restored);
    appendLog(`${u.name} 的 SP 崩溃：下个己方回合自动恢复至 ${u.spPendingRestore}`);
  }
  if(u.sp > 0 && u._spBroken) u._spBroken = false;
  if(u.sp > 0){
    refreshSpCrashVulnerability(u);
  }
}

function checkKhathiaFatigue(u){
  if(!u || u.id!=='khathia' || u.hp<=0) return;
  if(u._fatigueCrashLock) return;
  if(u.sp <= -100){
    u._fatigueCrashLock = true;
    appendLog(`${u.name} 的“疲劳的躯体”崩溃：SP 跌至 -100`);
    damageUnit(u.id, 50, 0, `${u.name} 疲劳崩溃`, u.id, {trueDamage:true, ignoreToughBody:true, skillFx:'khathia:疲劳崩溃'});
    applyStunOrStack(u, 1, {bypass:true, reason:'疲劳崩溃'});
    if(u.side==='enemy'){
      enemySteps = Math.max(0, enemySteps - 1);
      appendLog('疲劳崩溃：敌方额外 -1 步');
      updateStepsUI();
    } else {
      playerSteps = Math.max(0, playerSteps - 1);
      appendLog('疲劳崩溃：我方额外 -1 步');
      updateStepsUI();
    }
    u.sp = -25;
    u._fatigueCrashLock = false;
  }
}

function applyKhathiaDesignPenalty(){
  appendLog('糟糕的初始设计触发：所有单位 SP -10');
  for(const u of Object.values(units)){
    if(!u || u.hp<=0) continue;
    applySpDamage(u, 10, {reason:`${u.name} 被设计缺陷拖累：SP -{delta}`});
  }
}
function applySpDamage(targetOrId, amount, {sourceId=null, reason=null}={}){
  const u = typeof targetOrId === 'string' ? units[targetOrId] : targetOrId;
  if(!u || !u.hp<=0 || amount<=0) return 0;
  const before = u.sp;
  const floor = (typeof u.spFloor === 'number') ? u.spFloor : 0;
  u.sp = Math.max(floor, u.sp - amount);
  const delta = before - u.sp;
  if(delta>0){
    showDamageFloat(u,0,delta);
    if(reason){ appendLog(reason.replace('{delta}', String(delta))); }
    handleSpCrashIfNeeded(u);
    checkKhathiaFatigue(u);
    renderAll();
  }
  return delta;
}

// —— 伤害计算 —— 
function backstabMultiplier(attacker,target){
  const fromBehind = (target.facing === 'right' && attacker.c < target.c) || (target.facing === 'left' && attacker.c > target.c);
  if(fromBehind && attacker.side !== target.side){ appendLog('背刺触发 x1.5 伤害！'); return 1.5; }
  if(attacker.id === 'adora' && attacker.sp < 10) return 1.5;
  return 1.0;
}
function hasDeepBreathPassive(attacker){
  if(!attacker || attacker.id!=='karma') return false;
  const pool = attacker.skillPool || [];
  return pool.some(s=>s && s.name === '深呼吸');
}
function calcOutgoingDamage(attacker, baseDmg, target, skillName){
  let dmg = baseDmg;
  if(attacker.passives.includes('fearBuff') && attacker.sp<10) dmg = Math.round(dmg*1.5);
  if(attacker.passives.includes('pride')){
    const lostRatio = (attacker.maxHp - attacker.hp) / attacker.maxHp;
    dmg = Math.round(dmg * (1 + lostRatio * 0.5));
  }
  if(attacker.id==='karma' && skillName==='沙包大的拳头' && (attacker.consecAttacks||0)>=1){ dmg = Math.round(dmg*1.5); }
  if(attacker.id==='adora' && skillName==='短匕轻挥' && target){ dmg = Math.round(dmg * backstabMultiplier(attacker,target)); }
  if(hasDeepBreathPassive(attacker)){
    dmg = Math.round(dmg * 1.10);
  }
  return dmg;
}
function damageUnit(id, hpDmg, spDmg, reason, sourceId=null, opts={}){
  const u = units[id]; if(!u || u.hp<=0) return;

  const source = sourceId ? units[sourceId] : null;
  const buffStage = opts.buffStage || 'final';
  let trueDamage = !!opts.trueDamage;

  if(source && source !== u){
    const dirToTarget = cardinalDirFromDelta(u.r - source.r, u.c - source.c);
    setUnitFacing(source, dirToTarget);
  }

  if(source){
    if(source.side === u.side){ appendLog(`友伤无效：${source.name} -> ${u.name}`); return; }

    if(!opts.ignoreJixue && buffStage==='final' && source.status && source.status.jixueStacks>0){
      if(!source._jixueActivated){
        appendLog(`${source.name} 的“鸡血”触发：伤害 x2`);
        source._jixueActivated = true;
      }
      hpDmg = Math.round(hpDmg * 2);
    }

    if(!opts.ignoreDepend && buffStage==='final' && source.status && source.status.dependStacks>0){
      if(!source._dependUnleash){
        appendLog(`${source.name} 的“依赖”触发：造成真实伤害`);
        source._dependUnleash = true;
      }
      trueDamage = true;
    }
  }

  // 掩体：远程（距离>1）才被掩体免疫
  if(source && !trueDamage){
    if(isCoverCell(u.r, u.c) && mdist(source, u) > 1 && !opts.ignoreCover){
      appendLog(`${u.name} 处于掩体内，抵御了远距离伤害`);
      return;
    }
  }
  // 姿态减伤（优先于 Tusk 固有护甲）
  if(!trueDamage && u._stanceType && u._stanceTurns>0 && u._stanceDmgRed>0){
    hpDmg = Math.round(hpDmg * (1 - u._stanceDmgRed));
    spDmg = Math.round(spDmg * (1 - u._stanceDmgRed));
  }
  if(!trueDamage && u.id==='khathia'){
    if(Math.random() < 0.15){
      appendLog(`${u.name} 的“变态躯体”发动：完全免疫本次伤害`);
      showStatusFloat(u,'免疫',{type:'buff', offsetY:-48});
      pulseCell(u.r,u.c);
      renderAll();
      return;
    }
    hpDmg = Math.round(hpDmg * 0.75);
    spDmg = Math.round(spDmg * 0.75);
  }
  if(!trueDamage && u.passives.includes('toughBody') && !opts.ignoreToughBody){
    hpDmg = Math.round(hpDmg * 0.75);
  }

  if(u._spCrashVuln && (hpDmg>0 || spDmg>0)){
    hpDmg = Math.round(hpDmg * 2);
    spDmg = Math.round(spDmg * 2);
    appendLog(`${u.name} 因 SP 崩溃眩晕承受双倍伤害！`);
  }

  const prevHp = u.hp;
  const finalHp = Math.max(0, hpDmg);
  const finalSp = Math.max(0, spDmg);

  u.hp = Math.max(0, u.hp - finalHp);
  const floor = (typeof u.spFloor === 'number') ? u.spFloor : 0;
  u.sp = Math.max(floor, u.sp - finalSp);
  checkKhathiaFatigue(u);
  const died = prevHp > 0 && u.hp <= 0;

  const totalImpact = finalHp + finalSp;
  const heavyHit = trueDamage || totalImpact >= 40 || finalHp >= Math.max(18, Math.round(u.maxHp * 0.3));
  appendLog(`${reason} (-${finalHp} HP, -${finalSp} SP)`);
  cameraShake(heavyHit ? 'heavy' : 'normal');
  const skillFxKey = opts.skillFx || (opts.skillName && source ? `${source.id}:${opts.skillName}` : null);
  if(skillFxKey){
    const fxCtx = Object.assign({}, opts.skillFxCtx || {});
    if(fxCtx.attacker === undefined) fxCtx.attacker = source;
    if(fxCtx.target === undefined) fxCtx.target = u;
    if(fxCtx.cell === undefined && opts.fxCell) fxCtx.cell = opts.fxCell;
    if(fxCtx.point === undefined && opts.fxPoint) fxCtx.point = opts.fxPoint;
    if(opts.skillFxAngle !== undefined) fxCtx.angle = opts.skillFxAngle;
    fxCtx.trueDamage = trueDamage;
    fxCtx.heavy = heavyHit;
    showSkillFx(skillFxKey, fxCtx);
  } else {
    showAttackFx({attacker: source, target: u, trueDamage, heavy: heavyHit});
  }
  showDamageFloat(u, finalHp, finalSp);
  pulseCell(u.r, u.c);
  if(died){ showDeathFx(u); }

  // 反伤姿态：反弹部分HP伤害
  if(sourceId && u._stanceType==='retaliate' && u._stanceTurns>0 && u._reflectPct>0 && !opts._reflected){
    const refl = Math.max(0, Math.round(finalHp * u._reflectPct));
    if(refl>0){
      const src = units[sourceId];
      if(src && src.hp>0){
        appendLog(`${u.name} 的反伤姿态：反弹 ${refl} 伤害给 ${src.name}`);
        damageUnit(src.id, refl, 0, `反伤姿态反弹自 ${u.name}`, u.id, {...opts, _reflected:true, ignoreCover:true, ignoreToughBody:true});
      }
    }
  }

  if(sourceId){
    const src = units[sourceId];
    if(src && src.id==='khathia' && src!==u && src.hp>0 && (finalHp>0 || finalSp>0)){
      const beforeSp = src.sp;
      src.sp = Math.min(src.maxSp, src.sp + 2);
      const gain = src.sp - beforeSp;
      if(gain>0){
        showGainFloat(src,0,gain);
        appendLog(`${src.name} 的“老干部”触发：SP +${gain}`);
        checkKhathiaFatigue(src);
      }
    }
  }

  handleSpCrashIfNeeded(u);

  renderAll();
}

// —— 公用 FX —— 
function showTrail(r1,c1,r2,c2,{thickness=6,color=null}={}){
  ensureFxLayer();
  const p1=getCellCenter(r1,c1), p2=getCellCenter(r2,c2);
  const dx=p2.x-p1.x, dy=p2.y-p1.y;
  const len=Math.hypot(dx,dy);
  const ang=Math.atan2(dy,dx)*180/Math.PI;
  const trail=makeEl('fx-trail');
  if(color){ trail.style.background=color; }
  trail.style.left=`${p1.x}px`;
  trail.style.top =`${p1.y}px`;
  trail.style.width=`${thickness}px`;
  trail.style.transformOrigin='0 0';
  trail.style.transform=`translate(0,-${Math.max(1, Math.floor(thickness/2))}px) rotate(${ang}deg) scaleY(${len/thickness})`;
  fxLayer.appendChild(trail);
  onAnimEndRemove(trail, 260);
}

// —— 玩家/敌方技能 —— 
function playerGunExec(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  setUnitFacing(u, dir);
  const muzzle = forwardCellAt(u, dir, 1) || {r:u.r,c:u.c};
  cameraFocusOnCell(muzzle.r, muzzle.c);
  const line = forwardLineAt(u,dir);
  for(const cell of line){
    const tu = getUnitAt(cell.r,cell.c);
    showTrail(muzzle.r, muzzle.c, cell.r, cell.c);
    if(tu && tu.hp>0 && tu.side !== u.side){
      damageUnit(tu.id,10,5,`${u.name} 的 枪击 命中 ${tu.name}`, u.id,{skillFx:`${u.id}:枪击`});
      u.dmgDone += 10;
    }
  }
  unitActed(u);
}
function adoraDagger(u,target){
  if(!target || target.side===u.side){ appendLog('短匕轻挥 目标无效'); return; }
  const dmg = calcOutgoingDamage(u,10,target,'短匕轻挥');
  cameraFocusOnCell(target.r, target.c);
  damageUnit(target.id, dmg, 5, `${u.name} 用 短匕轻挥 攻击 ${target.name}`, u.id,{skillFx:'adora:短匕轻挥'});
  u.dmgDone += dmg; unitActed(u);
}
function adoraPanicMove(u, payload){
  const dest = payload && payload.moveTo; if(!dest){ appendLog('无效的目的地'); return; }
  cameraFocusOnCell(dest.r, dest.c); showTrail(u.r,u.c,dest.r,dest.c);
  if(dest.r !== u.r || dest.c !== u.c){
    const dir = cardinalDirFromDelta(dest.r - u.r, dest.c - u.c);
    setUnitFacing(u, dir);
  }
  u.r=dest.r; u.c=dest.c; pulseCell(u.r,u.c);
  registerUnitMove(u);
  showSkillFx('adora:呀！你不要靠近我呀！！',{target:u});
  for(const d of Object.keys(DIRS)){
    const cell = forwardCellAt(u,d,1); if(!cell) continue;
    const t = getUnitAt(cell.r,cell.c);
    if(t && t.side!==u.side && t.hp>0 && t.hp <= t.maxHp/2){ appendLog(`${u.name} 追击残血！`); adoraDagger(u,t); break; }
  }
  unitActed(u);
}
function adoraZap(u,target){
  if(!target || target.side===u.side){ appendLog('电击装置 目标无效'); return; }
  cameraFocusOnCell(target.r, target.c);
  damageUnit(target.id,10,15,`${u.name} 自制粉色迷你电击装置 命中 ${target.name}`, u.id,{skillFx:'adora:自制粉色迷你电击装置'});
  applyStunOrStack(target, 1, {reason:'电击装置'});
  addStatusStacks(target,'paralyzed',1,{label:'恐惧', type:'debuff'});
  appendLog(`${target.name} 下回合 -1 步`);
  u.dmgDone += 10; unitActed(u);
}
function adoraCheer(u, aim){
  const t = getUnitAt(aim.r, aim.c);
  if(!t || t.side!==u.side){ appendLog('加油哇！ 目标无效'); return; }
  if(t.status.jixueStacks>0){ appendLog(`${t.name} 已经处于“鸡血”状态`); return; }
  updateStatusStacks(t,'jixueStacks',1,{label:'鸡血', type:'buff'});
  pulseCell(t.r,t.c);
  showSkillFx('adora:加油哇！',{target:t});
  appendLog(`${u.name} 对 ${t.name} 使用 加油哇！：赋予 1 层“鸡血”`);
  unitActed(u);
}
function darioClaw(u,target){
  if(!target || target.side===u.side){ appendLog('机械爪击 目标无效'); return; }
  const dmg = calcOutgoingDamage(u,15,target,'机械爪击');
  cameraFocusOnCell(target.r, target.c);
  damageUnit(target.id, dmg, 0, `${u.name} 发动 机械爪击 ${target.name}`, u.id,{skillFx:'dario:机械爪击'});
  u.dmgDone += dmg; unitActed(u);
}
function darioSwiftMove(u, payload){
  const dest = payload && payload.moveTo; if(!dest){ appendLog('无效的目的地'); return; }
  cameraFocusOnCell(dest.r, dest.c); showTrail(u.r,u.c,dest.r,dest.c);
  if(dest.r !== u.r || dest.c !== u.c){
    const dir = cardinalDirFromDelta(dest.r - u.r, dest.c - u.c);
    setUnitFacing(u, dir);
  }
  u.r=dest.r; u.c=dest.c; pulseCell(u.r,u.c);
  registerUnitMove(u);
  showSkillFx('dario:迅捷步伐',{target:u});
  const enemies = Object.values(units).filter(x=>x.side!==u.side && x.hp>0);
  if(enemies.length){
    let target=null, best=1e9;
    for(const e of enemies){ const d=mdist(u,e); if(d<best){best=d; target=e;} }
    const reduced = applySpDamage(target, 5, {sourceId:u.id});
    appendLog(`${target.name} SP -${reduced}（迅捷步伐）`);
    showSkillFx('dario:迅捷步伐',{target:target});
  }
  unitActed(u);
}
function darioPull(u, targetOrDesc){
  let target = null, usedDir = null;
  if(targetOrDesc && targetOrDesc.id){ target = targetOrDesc; usedDir = cardinalDirFromDelta(target.r - u.r, target.c - u.c); }
  else if(targetOrDesc && targetOrDesc.dir){ usedDir = targetOrDesc.dir; const line = forwardLineAt(u, usedDir); for(const cell of line){ const tu=getUnitAt(cell.r,cell.c); if(tu && tu.hp>0 && tu.side!==u.side){ target=tu; break; } } }
  if(!target){ appendLog('拿来吧你！ 未找到可拉拽目标'); return; }
  cameraFocusOnCell(target.r, target.c);
  if(target.pullImmune){ appendLog(`${target.name} 免疫拉扯（小Boss/Boss），改为冲击效果`); }
  else {
    let placement = null;
    if(usedDir){
      const line = forwardLineAt(u, usedDir);
      for(const cell of line){ const occ = getUnitAt(cell.r, cell.c); if(!occ){ placement = cell; break; } }
    }
    if(placement){
      appendLog(`${u.name} 将 ${target.name} 拉到 (${placement.r}, ${placement.c})`);
      showTrail(target.r, target.c, placement.r, placement.c);
      target.r = placement.r; target.c = placement.c; pulseCell(target.r, target.c);
    } else {
      appendLog('前方无空位，改为直接造成冲击效果');
    }
  }
  const dmg = calcOutgoingDamage(u,20,target,'拿来吧你！');
  damageUnit(target.id, dmg, 0, `${u.name} 的 拿来吧你！ 命中 ${target.name}`, u.id,{skillFx:'dario:拿来吧你！'});
  applyStun