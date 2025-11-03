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
const KHATHIA_FATIGUE_STUN_DURATION = 3;

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
    sp: (typeof extra.initialSp === 'number') ? extra.initialSp : maxSp, maxSp,
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
    _usedSkillThisTurn: false,
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
units['khathia'] = createUnit('khathia','Khathia','enemy',35, 4, 19, 700, 0, 0, 0, ['khathiaVeteran','khathiaTwisted','khathiaFatigue','khathiaDesign'], {
  size:2,
  stunThreshold:4,
  spFloor:-100,
  disableSpCrash:true,
  maxMovePerTurn:3,
  initialSp:0,
  pullImmune:true,
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
// 2x2 单位前方矩形区域（对齐边缘，横向宽度 x 前向深度）
function forwardRect2x2(u, dir, lateralWidth, depth){
  if(u.size !== 2) return forwardRectCentered(u, dir, lateralWidth, depth);
  
  const res=[];
  const d = DIRS[dir];
  
  // 对于2x2单位，计算攻击起始边缘
  // 单位占据 (u.r, u.c), (u.r+1, u.c), (u.r, u.c+1), (u.r+1, u.c+1)
  
  if(dir === 'left'){
    // 攻击左侧，从 (u.r, u.c-1) 和 (u.r+1, u.c-1) 开始
    const startC = u.c - 1;
    for(let step = 0; step < depth; step++){
      const c = startC - step;
      for(let extraR = 0; extraR < lateralWidth; extraR++){
        const r = u.r + extraR - Math.floor((lateralWidth - 2) / 2);
        if(clampCell(r, c)) res.push({r, c, dir});
      }
    }
  } else if(dir === 'right'){
    // 攻击右侧，从 (u.r, u.c+2) 和 (u.r+1, u.c+2) 开始
    const startC = u.c + 2;
    for(let step = 0; step < depth; step++){
      const c = startC + step;
      for(let extraR = 0; extraR < lateralWidth; extraR++){
        const r = u.r + extraR - Math.floor((lateralWidth - 2) / 2);
        if(clampCell(r, c)) res.push({r, c, dir});
      }
    }
  } else if(dir === 'up'){
    // 攻击上方，从 (u.r-1, u.c) 和 (u.r-1, u.c+1) 开始
    const startR = u.r - 1;
    for(let step = 0; step < depth; step++){
      const r = startR - step;
      for(let extraC = 0; extraC < lateralWidth; extraC++){
        const c = u.c + extraC - Math.floor((lateralWidth - 2) / 2);
        if(clampCell(r, c)) res.push({r, c, dir});
      }
    }
  } else if(dir === 'down'){
    // 攻击下方，从 (u.r+2, u.c) 和 (u.r+2, u.c+1) 开始
    const startR = u.r + 2;
    for(let step = 0; step < depth; step++){
      const r = startR + step;
      for(let extraC = 0; extraC < lateralWidth; extraC++){
        const c = u.c + extraC - Math.floor((lateralWidth - 2) / 2);
        if(clampCell(r, c)) res.push({r, c, dir});
      }
    }
  }
  
  return res;
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
                      background: linear-gradient(180deg, rgba(255,255,255,0) 0%, rgba(255,255,255,0.9) 35%, rgba(255,128,17,0.9) 68%, rgba(255,255,255,0) 100%);
                      opacity: 0; transform-origin: 50% 100%; }
  .fx-attack.true-damage .slash { background: linear-gradient(180deg, rgba(255,255,255,0) 0%, rgba(255,255,255,0.92) 35%, rgba(145,102,255,0.94) 68%, rgba(255,255,255,0) 100%); }
  .fx-attack .slash.main { animation: fx-attack-slash 420ms ease-out forwards; }
  .fx-attack .slash.reverse { animation: fx-attack-slash-rev 420ms ease-out forwards; }
  .fx-attack .ring { position: absolute; left: 50%; top: 50%; width: 56%; height: 56%; border-radius: 50%; border: 3px solid rgba(255,198,73,0.95);
                     transform: translate(-50%, -50%) scale(0.4); opacity: 0; box-shadow: 0 0 22px rgba(255,157,46,0.45);
                     animation: fx-attack-ring 520ms ease-out forwards; }
  .fx-attack.true-damage .ring { border-color: rgba(155,110,255,0.95); box-shadow: 0 0 26px rgba(155,110,255,0.55); }
  .fx-attack .spark { position: absolute; left: 50%; top: 50%; width: 14px; height: 14px; border-radius: 50%;
                      background: radial-gradient(circle, rgba(255,255,255,0.95) 0%, rgba(255,255,255,0) 65%);
                      opacity: 0; transform-origin: 0 0; --spark-angle: 0deg;
                      animation: fx-attack-spark 480ms ease-out forwards; }
  .fx-attack.true-damage .spark { background: radial-gradient(circle, rgba(255,255,255,0.95) 0%, rgba(166,93,255,0) 65%); }
  .fx-attack .spark.left { --spark-angle: -40deg; }
  .fx-attack .spark.right { --spark-angle: 140deg; }
  .skill-fx { position: absolute; transform: translate(-50%, -50%); pointer-events: none; mix-blend-mode: screen; opacity: 0;
              filter: drop-shadow(0 12px 26px rgba(0,0,0,0.55)); animation: skill-fx-fade 680ms ease-out forwards; }
  .skill-fx .glyph { font-weight: 800; font-size: 26px; letter-spacing: 1px; color: var(--skill-outline, rgba(255,255,255,0.85));
                     text-shadow: 0 0 12px rgba(255,255,255,0.35); }
  .skill-fx.slash { width: 160px; height: 160px; }
  .skill-fx.slash .flash { position: absolute; left: 50%; top: 50%; width: 62%; height: 62%; border-radius: 50%; opacity: 0;
                            background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,255,0.8)) 0%, rgba(255,255,255,0) 70%);
                            transform: translate(-50%, -50%) scale(0.4); animation: skill-slash-flash 420ms ease-out forwards; }
  .skill-fx.slash .ring { position: absolute; left: 50%; top: 50%; width: 56%; height: 56%; border-radius: 50%;
                          border: 3px solid var(--skill-secondary, rgba(255,255,255,0.65)); opacity: 0;
                          transform: translate(-50%, -50%) scale(0.35);
                          box-shadow: 0 0 18px var(--skill-secondary, rgba(255,255,255,0.35)); animation: skill-slash-ring 520ms ease-out forwards; }
  .skill-fx.slash .sparks { position: absolute; inset: 0; }
  .skill-fx.slash .spark { position: absolute; left: 50%; top: 50%; width: 16px; height: 16px; border-radius: 50%; opacity: 0;
                           background: radial-gradient(circle, rgba(255,255,255,0.95) 0%, rgba(255,255,255,0) 70%);
                           transform-origin: 0 0; animation: skill-slash-spark 480ms ease-out forwards; }
  .skill-fx.slash .spark.left { --spark-angle: -50deg; }
  .skill-fx.slash .spark.right { --spark-angle: 140deg; }
  .skill-fx.slash .strokes { position: absolute; inset: 0; }
  .skill-fx.slash .stroke { position: absolute; left: 50%; top: 50%; width: 26px; height: 120%; border-radius: 999px; opacity: 0;
                            transform-origin: 50% 100%; background: linear-gradient(180deg, rgba(255,255,255,0), var(--skill-primary, rgba(255,255,255,0.92)) 45%, rgba(255,255,255,0));
                            animation: skill-slash-stroke 520ms ease-out forwards; }
  .skill-fx.slash .stroke[data-index="0"] { --stroke-offset: -18deg; --stroke-shift: -6deg; }
  .skill-fx.slash .stroke[data-index="1"] { --stroke-offset: 0deg; --stroke-shift: 0deg; animation-delay: 40ms; }
  .skill-fx.slash .stroke[data-index="2"] { --stroke-offset: 20deg; --stroke-shift: 8deg; animation-delay: 70ms; }
  .skill-fx.claw { width: 160px; height: 160px; }
  .skill-fx.claw .burst { position: absolute; left:50%; top:50%; width: 68%; height:68%; border-radius: 50%; opacity:0.8;
                           transform: translate(-50%,-50%) scale(0.4);
                           background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,255,0.7)) 0%, rgba(255,255,255,0) 70%);
                           animation: skill-claw-burst 520ms ease-out forwards; }
  .skill-fx.claw[data-variant="mecha"] .burst { box-shadow: 0 0 22px var(--skill-primary, rgba(255,255,255,0.6));
                                                 background: radial-gradient(circle, rgba(255,255,255,0.65) 0%, var(--skill-secondary, rgba(255,255,255,0.0)) 70%); }
  .skill-fx.claw .scratch { position:absolute; left:50%; top:50%; width:12px; height:120%; opacity:0; transform-origin:50% 0;
                             animation: skill-claw-scratch 560ms ease-out forwards; }
  .skill-fx.claw .scratch span { display:block; width:100%; height:100%; border-radius:999px;
                                 background: linear-gradient(180deg, rgba(255,255,255,0.05), var(--skill-primary,#ffffff) 55%, rgba(255,255,255,0));
                                 box-shadow: 0 0 16px var(--skill-primary, rgba(255,255,255,0.35)); }
  .skill-fx.claw .shard { position:absolute; left:50%; top:50%; width:18px; height:38px; border-radius:999px; opacity:0;
                          transform-origin:50% 90%; background: linear-gradient(180deg, rgba(255,255,255,0.3), var(--skill-primary, rgba(255,255,255,0.9)) 60%, rgba(255,255,255,0));
                          filter: drop-shadow(0 0 10px rgba(255,255,255,0.45)); animation: skill-claw-shard 520ms ease-out forwards; }
  .skill-fx.claw[data-variant="mecha"] .servo-ring { position:absolute; left:50%; top:50%; width:130%; height:130%; border-radius:50%;
                                                       border:3px solid var(--skill-primary, rgba(255,255,255,0.85)); opacity:0;
                                                       transform: translate(-50%, -50%) scale(0.4);
                                                       box-shadow: 0 0 18px var(--skill-secondary, rgba(255,255,255,0.35));
                                                       animation: skill-claw-servo 620ms ease-out forwards; }
  .skill-fx.claw[data-variant="mecha"] .servo-flare { position:absolute; left:50%; top:50%; width:84%; height:84%; border-radius:50%; opacity:0;
                                                        transform: translate(-50%, -50%) scale(0.5);
                                                        background: radial-gradient(circle, rgba(255,255,255,0.7) 0%, rgba(255,255,255,0) 70%);
                                                        animation: skill-claw-servo-flare 600ms ease-out forwards; }
  .skill-fx.claw[data-variant="mecha"] .mecha-sparks { position:absolute; inset:0; }
  .skill-fx.claw[data-variant="mecha"] .mecha-sparks .spark { position:absolute; left:50%; top:50%; width:18px; height:18px; border-radius:50%;
                                                                background: radial-gradient(circle, rgba(255,255,255,0.95) 0%, rgba(255,255,255,0) 70%);
                                                                opacity:0; transform-origin:0 0; animation: skill-claw-mecha-spark 520ms ease-out forwards; }
  .skill-fx.claw[data-variant="mecha"] .mecha-sparks .spark.one { --spark-angle: -35deg; }
  .skill-fx.claw[data-variant="mecha"] .mecha-sparks .spark.two { --spark-angle: 145deg; animation-delay: 70ms; }
  .skill-fx.claw .scratch[data-index="0"] { --scratch-shift:-28px; }
  .skill-fx.claw .scratch[data-index="1"] { --scratch-shift:-12px; animation-delay: 30ms; }
  .skill-fx.claw .scratch[data-index="2"] { --scratch-shift: 6px; animation-delay: 60ms; }
  .skill-fx.claw .scratch[data-index="3"] { --scratch-shift: 22px; animation-delay: 90ms; }
  .skill-fx.claw .scratch[data-index="4"] { --scratch-shift: 38px; animation-delay: 120ms; }
  .skill-fx.attack-swing { width: 150px; height: 150px; }
  .skill-fx.attack-swing .glow { position:absolute; left:50%; top:50%; width:82%; height:82%; border-radius:50%; opacity:0;
                                 transform: translate(-50%, -50%) scale(0.3);
                                 background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,255,0.6)) 0%, rgba(255,255,255,0) 70%);
                                 animation: attack-swing-glow 420ms ease-out forwards; }
  .skill-fx.attack-swing .arc { position:absolute; left:50%; top:50%; width:18px; height:94%; border-radius:999px; opacity:0;
                                transform-origin:50% 88%;
                                background: linear-gradient(180deg, rgba(255,255,255,0.0), var(--skill-primary, rgba(255,255,255,0.95)) 52%, rgba(255,255,255,0));
                                box-shadow: 0 0 18px var(--skill-primary, rgba(255,255,255,0.4));
                                animation: attack-swing-arc 420ms ease-out forwards; }
  .skill-fx.attack-swing[data-variant="claw"] .arc { height: 100%; width: 16px; transform-origin:50% 90%; }
  .skill-fx.attack-swing[data-variant="mecha"] .arc { box-shadow: 0 0 22px var(--skill-primary, rgba(255,255,255,0.55)); }
  .skill-fx.attack-swing[data-variant="wide"] .arc { height: 110%; }
  .skill-fx.attack-swing .arc { transform: translate(-50%, -50%) rotate(calc(var(--attack-angle, 0deg) + var(--arc-angle-offset, 0deg))); }
  .skill-fx.attack-muzzle { width: calc(var(--attack-length, 90px) + 50px); height: 86px;
                            transform: translate(-50%, -50%) rotate(var(--attack-angle, 0deg)); }
  .skill-fx.attack-muzzle .flash { position:absolute; left:24%; top:50%; width:48px; height:48px; border-radius:50%; opacity:0.9;
                                   transform: translate(-50%, -50%) scale(0.4);
                                   background: radial-gradient(circle, var(--skill-primary, rgba(255,255,255,0.85)) 0%, rgba(255,255,255,0) 72%);
                                   box-shadow: 0 0 24px var(--skill-primary, rgba(255,255,255,0.55));
                                   animation: attack-muzzle-flash 360ms ease-out forwards; }
  .skill-fx.attack-muzzle .trail { position:absolute; left:50%; top:50%; height:12px; width: var(--attack-length, 90px);
                                   border-radius: 999px; opacity:0;
                                   transform: translate(-10%, -50%);
                                   background: linear-gradient(90deg, rgba(255,255,255,0.0) 0%, var(--skill-primary, rgba(255,255,255,0.85)) 45%, rgba(255,255,255,0) 100%);
                                   box-shadow: 0 0 18px var(--skill-secondary, rgba(255,255,255,0.4));
                                   animation: attack-muzzle-trail 420ms ease-out forwards; }
  .skill-fx.attack-aura { width: 150px; height: 150px; }
  .skill-fx.attack-aura .ring { position:absolute; left:50%; top:50%; width:86%; height:86%; border-radius:50%; opacity:0;
                                 transform: translate(-50%, -50%) scale(0.35);
                                 border:2px solid var(--skill-primary, rgba(255,255,255,0.8));
                                 box-shadow: 0 0 18px var(--skill-secondary, rgba(255,255,255,0.35));
                                 animation: attack-aura-ring 520ms ease-out forwards; }
  .skill-fx.attack-aura .pulse { position:absolute; left:50%; top:50%; width:64%; height:64%; border-radius:50%; opacity:0;
                                 transform: translate(-50%, -50%) scale(0.5);
                                 background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,255,0.55)) 0%, rgba(255,255,255,0) 72%);
                                 animation: attack-aura-pulse 520ms ease-out forwards; }
  .skill-fx.beam { width: calc(var(--skill-length, 140px) + 60px); height: 80px; }
  .skill-fx.beam .muzzle { position:absolute; left:50%; top:50%; width:52px; height:52px; border-radius:50%; opacity:0.8;
                           transform: translate(-50%,-50%) scale(0.35);
                           background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,255,0.85)) 0%, rgba(255,255,255,0) 70%);
                           animation: skill-beam-muzzle 360ms ease-out forwards; }
  .skill-fx.beam .trail { position:absolute; left:50%; top:50%; height:12px; width: var(--skill-length, 140px);
                          background: linear-gradient(90deg, var(--skill-secondary, rgba(255,255,255,0.45)) 0%, var(--skill-primary, rgba(255,255,255,0.95)) 70%, rgba(255,255,255,0) 100%);
                          border-radius: 999px; opacity:0; transform-origin:0 50%; animation: skill-beam-trail 360ms ease-out forwards; }
  .skill-fx.beam .flare { position:absolute; right:8%; top:50%; width:42px; height:42px; border-radius:50%; opacity:0;
                          background: radial-gradient(circle, rgba(255,255,255,0.85) 0%, transparent 70%);
                          animation: skill-beam-flare 380ms ease-out forwards; }
  .skill-fx.burst { width: 200px; height: 200px; }
  .skill-fx.burst .ring { position:absolute; left:50%; top:50%; width:70%; height:70%; border-radius:50%; border:3px solid var(--skill-primary,#ffffff);
                          transform:translate(-50%,-50%) scale(0.4); opacity:0; animation: skill-burst-ring 620ms ease-out forwards; }
  .skill-fx.burst .wave { position:absolute; left:50%; top:50%; width:96%; height:96%; border-radius:50%; opacity:0;
                          background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,255,0.6)) 0%, rgba(255,255,255,0) 80%);
                          transform:translate(-50%,-50%) scale(0.3); animation: skill-burst-wave 660ms ease-out forwards; }
  .skill-fx.burst .core { position:absolute; left:50%; top:50%; width:38%; height:38%; border-radius:50%; opacity:0.9;
                          transform:translate(-50%,-50%); background: radial-gradient(circle, rgba(255,255,255,0.92) 0%, var(--skill-primary, rgba(255,255,255,0.85)) 80%);
                          animation: skill-burst-core 420ms ease-out forwards; }
  .skill-fx.aura { width: 170px; height: 170px; filter: drop-shadow(0 0 16px var(--skill-primary, rgba(255,255,255,0.35))); }
  .skill-fx.aura .halo { position:absolute; left:50%; top:50%; width:86%; height:86%; border-radius:50%; opacity:0;
                          transform:translate(-50%,-50%) scale(0.6);
                          background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,255,0.75)) 0%, rgba(255,255,255,0) 75%);
                          animation: skill-aura-halo 760ms ease-out forwards; }
  .skill-fx.aura .glyph { position:absolute; left:50%; top:50%; transform:translate(-50%,-50%); opacity:0;
                          animation: skill-aura-glyph 720ms ease-out forwards; }
  .skill-fx.aura .particles { position:absolute; inset:0; background: radial-gradient(circle, var(--skill-primary, rgba(255,255,255,0.35)) 0%, rgba(255,255,255,0) 70%);
                              border-radius:50%; opacity:0.6; filter: blur(12px); animation: skill-aura-pulse 780ms ease-out forwards; }
  .skill-fx.lightning { width: 180px; height: 180px; }
  .skill-fx.lightning .glow { position:absolute; left:50%; top:50%; width:80%; height:80%; border-radius:50%; opacity:0.8;
                               transform:translate(-50%,-50%) scale(0.4); background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,255,0.85)) 0%, rgba(255,255,255,0) 75%);
                               animation: skill-lightning-glow 520ms ease-out forwards; }
  .skill-fx.lightning .bolt { position:absolute; left:50%; top:50%; width:6px; height:110%; opacity:0;
                              background: linear-gradient(180deg, rgba(255,255,255,0), var(--skill-primary,#ffffff) 45%, rgba(255,255,255,0));
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
                          background: radial-gradient(circle, rgba(255,255,255,0.92) 0%, var(--skill-primary, rgba(255,255,255,0.82)) 80%);
                          transform:translate(-50%,-50%); animation: skill-rune-flare 520ms ease-out forwards; }
  .skill-fx.impact { width: 180px; height: 180px; }
  .skill-fx.impact .shock { position:absolute; left:50%; top:50%; width:70%; height:70%; border-radius:50%; opacity:0;
                             background: radial-gradient(circle, var(--skill-primary, rgba(255,255,255,0.75)) 0%, rgba(255,255,255,0) 80%);
                             transform:translate(-50%,-50%) scale(0.45); animation: skill-impact-shock 640ms ease-out forwards; }
  .skill-fx.impact .dust { position:absolute; left:50%; top:65%; width:120%; height:40%; opacity:0.7;
                           background: radial-gradient(circle, var(--skill-secondary, rgba(255,255,255,0.6)) 0%, rgba(255,255,255,0) 80%);
                           transform:translate(-50%,-50%) scaleX(0.4); animation: skill-impact-dust 720ms ease-out forwards; filter: blur(6px); }
  .skill-fx.impact .cracks { position:absolute; left:50%; top:50%; width:80%; height:80%; opacity:0;
                             background: radial-gradient(circle, rgba(255,255,255,0.75) 0%, rgba(255,255,255,0) 75%);
                             transform:translate(-50%,-50%) scale(0.3); mask: radial-gradient(circle, transparent 45%, #000 46%);
                             animation: skill-impact-crack 620ms ease-out forwards; }
  .skill-fx.cascade { width: 130px; height: 200px; }
  .skill-fx.cascade .column { position:absolute; left:50%; top:0; width:46px; height:100%; opacity:0.75;
                               background: linear-gradient(180deg, var(--skill-primary, rgba(255,255,255,0.7)) 0%, rgba(255,255,255,0) 85%);
                               transform:translateX(-50%); animation: skill-cascade-column 720ms ease-out forwards; }
  .skill-fx.cascade .drop { position:absolute; left:50%; width:14px; height:24px; border-radius:999px;
                             background: radial-gradient(circle, rgba(255,255,255,0.9) 0%, var(--skill-secondary, rgba(255,255,255,0.65)) 70%);
                             opacity:0; animation: skill-cascade-drop 680ms ease-out forwards; }
  .skill-fx.cascade .drop[data-index="0"] { top:10%; animation-delay: 20ms; }
  .skill-fx.cascade .drop[data-index="1"] { top:32%; animation-delay: 70ms; }
  .skill-fx.cascade .drop[data-index="2"] { top:56%; animation-delay: 110ms; }
  .skill-fx.cascade .drop[data-index="3"] { top:74%; animation-delay: 150ms; }
  .skill-fx.cascade .drop[data-index="4"] { top:20%; animation-delay: 200ms; }
  .skill-fx.cascade .drop[data-index="5"] { top:44%; animation-delay: 240ms; }
  .skill-fx.spiral { width: 180px; height: 180px; }
  .skill-fx.spiral .swirl { position:absolute; left:50%; top:50%; width:80%; height:80%; border-radius:50%; border:4px solid var(--skill-primary, rgba(255,255,255,0.7));
                             transform:translate(-50%,-50%) scale(0.3); opacity:0; animation: skill-spiral-spin 640ms ease-out forwards; }
  .skill-fx.spiral .swirl.two { border-color: var(--skill-secondary, rgba(255,255,255,0.7)); animation-delay: 80ms; }
  .skill-fx.spiral .center { position:absolute; left:50%; top:50%; width:32%; height:32%; border-radius:50%; opacity:0.9;
                              background: radial-gradient(circle, rgba(255,255,255,0.92) 0%, var(--skill-secondary, rgba(255,255,255,0.75)) 90%);
                              transform:translate(-50%,-50%); animation: skill-spiral-center 540ms ease-out forwards; }
  .fx-death { position: absolute; transform: translate(-50%, -50%); pointer-events: none; overflow: visible;
              filter: drop-shadow(0 14px 28px rgba(0,0,0,0.45)); animation: fx-death-fade 900ms ease-out forwards; }
  .fx-death .piece { position: absolute; left: 0; width: 100%; height: 50%; box-sizing: border-box; border-radius: 8px;
                     background: rgba(255,255,255,0.14); border: 1px solid rgba(255,255,255,0.28); }
  .fx-death.player .piece { background: rgba(91,140,255,0.18); border-color: rgba(91,140,255,0.45); }
  .fx-death.enemy  .piece { background: rgba(255,77,79,0.18); border-color: rgba(255,77,79,0.45); }
  .fx-death .piece.top { top: 0; border-bottom-left-radius: 4px; border-bottom-right-radius: 4px;
                         animation: fx-death-top 900ms ease-out forwards; }
  .fx-death .piece.bottom { bottom: 0; border-top-left-radius: 4px; border-top-right-radius: 4px;
                            animation: fx-death-bottom 900ms ease-out forwards; }
  .fx-death.size-2 .piece { border-radius: 12px; }
  .fx-death .crack { position: absolute; left: 50%; top: 0; width: 3px; height: 100%;
                     background: linear-gradient(180deg, rgba(255,255,255,0.95), rgba(255,255,255,0));
                     transform: translateX(-50%) scaleY(0); mix-blend-mode: screen;
                     animation: fx-death-crack 260ms ease-out forwards, fx-death-fade 900ms ease-out forwards; }
  .fx-death .dust { position: absolute; left: 50%; top: 50%; width: 100%; height: 100%;
                    background: radial-gradient(circle, rgba(255,255,255,0.28) 0%, rgba(255,255,255,0) 70%);
                    transform: translate(-50%, -50%) scale(0.65); opacity: 0.85;
                    animation: fx-death-dust 900ms ease-out forwards; pointer-events: none; }
  .fx-trail { width: 6px; height: 0; background: linear-gradient(90deg, rgba(255,255,255,0), rgba(255,255,255,0.85), rgba(255,255,255,0));
              box-shadow: 0 0 8px rgba(255,255,255,0.8); transform-origin: 0 0; animation: fx-trail 220ms linear forwards; mix-blend-mode: screen; }
  .shake { animation: cam-shake 180ms ease-in-out 1; }
  .shake-heavy { animation: cam-shake-heavy 320ms ease-in-out 1; }
  .pulse { animation: pulse 600ms ease-out 1; }
  @keyframes fx-pop { 0%{ transform: scale(0.7); opacity: 0.0; } 55%{ transform: scale(1.1); opacity: 1; } 100%{ transform: scale(1); opacity: 1; } }
  @keyframes fx-float-up { 0%{ transform: translate(-50%,-50%) translate(var(--fx-offset-x), var(--fx-offset-y)); opacity: 1; }
                           100%{ transform: translate(-50%,-50%) translate(var(--fx-offset-x), calc(var(--fx-offset-y) - 36px)); opacity: 0; } }
  @keyframes fx-attack-fade { 0% { opacity: 0; transform: translate(-50%, -50%) scale(calc(var(--attack-scale, 1) * 0.75)); }
                               35% { opacity: 1; transform: translate(-50%, -50%) scale(calc(var(--attack-scale, 1) * 1.06)); }
                               100% { opacity: 0; transform: translate(-50%, -50%) scale(calc(var(--attack-scale, 1) * 0.92)); } }
  @keyframes fx-attack-flash { 0% { opacity: 0; transform: translate(-50%, -50%) scale(calc(var(--attack-scale, 1) * 0.35)); }
                               20% { opacity: 1; transform: translate(-50%, -50%) scale(calc(var(--attack-scale, 1) * 1.05)); }
                               100% { opacity: 0; transform: translate(-50%, -50%) scale(calc(var(--attack-scale, 1) * 0.8)); } }
  @keyframes fx-attack-slash { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(calc(var(--fx-angle, 0deg) - 26deg)) scaleY(0.1) scaleX(0.6); }
                               35% { opacity: 1; transform: translate(-50%, -50%) rotate(calc(var(--fx-angle, 0deg) - 6deg)) scaleY(1.2) scaleX(1); }
                               100% { opacity: 0; transform: translate(-50%, -50%) rotate(calc(var(--fx-angle, 0deg) + 14deg)) scaleY(0.4) scaleX(0.85); } }
  @keyframes fx-attack-slash-rev { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(calc(var(--fx-angle, 0deg) + 154deg)) scaleY(0.1) scaleX(0.5); }
                                   35% { opacity: 1; transform: translate(-50%, -50%) rotate(calc(var(--fx-angle, 0deg) + 174deg)) scaleY(1.1) scaleX(0.95); }
                                   100% { opacity: 0; transform: translate(-50%, -50%) rotate(calc(var(--fx-angle, 0deg) + 198deg)) scaleY(0.35) scaleX(0.8); } }
  @keyframes fx-attack-ring { 0% { opacity: 0; transform: translate(-50%, -50%) scale(calc(var(--attack-scale, 1) * 0.3)); }
                              30% { opacity: 1; transform: translate(-50%, -50%) scale(calc(var(--attack-scale, 1) * 1.05)); }
                              100% { opacity: 0; transform: translate(-50%, -50%) scale(calc(var(--attack-scale, 1) * 1.45)); } }
  @keyframes fx-attack-spark { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(var(--spark-angle, 0deg)) translateX(0) scale(0.3); }
                               35% { opacity: 1; }
                               100% { opacity: 0; transform: translate(-50%, -50%) rotate(var(--spark-angle, 0deg)) translateX(86px) scale(0.65); } }
  @keyframes attack-swing-glow { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.25); }
                                 35% { opacity: 0.85; transform: translate(-50%, -50%) scale(0.95); }
                                 100% { opacity: 0; transform: translate(-50%, -50%) scale(1.3); } }
  @keyframes attack-swing-arc { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(calc(var(--attack-angle,0deg) + var(--arc-angle-offset,0deg) - 26deg)) scaleY(0.25) scaleX(0.55); }
                                35% { opacity: 1; transform: translate(-50%, -50%) rotate(calc(var(--attack-angle,0deg) + var(--arc-angle-offset,0deg) - 6deg)) scaleY(1.15) scaleX(1.05); }
                                100% { opacity: 0; transform: translate(-50%, -50%) rotate(calc(var(--attack-angle,0deg) + var(--arc-angle-offset,0deg) + 16deg)) scaleY(0.45) scaleX(0.8); } }
  @keyframes attack-muzzle-flash { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.35); }
                                   30% { opacity: 1; transform: translate(-50%, -50%) scale(1.05); }
                                   100% { opacity: 0; transform: translate(-50%, -50%) scale(1.35); } }
  @keyframes attack-muzzle-trail { 0% { opacity: 0; width: 0; }
                                   35% { opacity: 1; width: var(--attack-length, 90px); }
                                   100% { opacity: 0; width: var(--attack-length, 90px); } }
  @keyframes attack-aura-ring { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.35); }
                                40% { opacity: 1; transform: translate(-50%, -50%) scale(1.05); }
                                100% { opacity: 0; transform: translate(-50%, -50%) scale(1.45); } }
  @keyframes attack-aura-pulse { 0% { opacity: 0.7; transform: translate(-50%, -50%) scale(0.6); }
                                 55% { opacity: 0.95; transform: translate(-50%, -50%) scale(1.0); }
                                 100% { opacity: 0; transform: translate(-50%, -50%) scale(1.3); } }
  @keyframes skill-fx-fade { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.82); }
                             22% { opacity: 1; }
                             100% { opacity: 0; transform: translate(-50%, -50%) scale(1.08); } }
  @keyframes skill-slash-flash { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.4); }
                                 35% { opacity: 1; transform: translate(-50%, -50%) scale(1.05); }
                                 100% { opacity: 0; transform: translate(-50%, -50%) scale(1.3); } }
  @keyframes skill-slash-ring { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.35); }
                                40% { opacity: 1; transform: translate(-50%, -50%) scale(1.0); }
                                100% { opacity: 0; transform: translate(-50%, -50%) scale(1.45); } }
  @keyframes skill-slash-spark { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(var(--spark-angle, 0deg)) translateX(0) scale(0.4); }
                                 35% { opacity: 1; }
                                 100% { opacity: 0; transform: translate(-50%, -50%) rotate(var(--spark-angle, 0deg)) translateX(90px) scale(0.7); } }
  @keyframes skill-slash-stroke { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(calc(var(--skill-angle,0deg) + var(--stroke-offset,0deg))) scaleY(0.2) scaleX(0.6); }
                                  35% { opacity: 1; transform: translate(-50%, -50%) rotate(calc(var(--skill-angle,0deg) + var(--stroke-offset,0deg) + var(--stroke-shift,0deg))) scaleY(1.25) scaleX(1.05); }
                                  100% { opacity: 0; transform: translate(-50%, -50%) rotate(calc(var(--skill-angle,0deg) + var(--stroke-offset,0deg) + 22deg)) scaleY(0.35) scaleX(0.8); } }
  @keyframes skill-claw-burst { 0% { opacity: 0.65; transform: translate(-50%, -50%) scale(0.35); }
                                60% { opacity: 0.9; transform: translate(-50%, -50%) scale(1.05); }
                                100% { opacity: 0; transform: translate(-50%, -50%) scale(1.4); } }
  @keyframes skill-claw-scratch { 0% { opacity: 0; transform: translate(calc(-50% + var(--scratch-shift,0px)), -60%) scaleY(0.3); }
                                   40% { opacity: 1; transform: translate(calc(-50% + var(--scratch-shift,0px)), 10%) scaleY(1.05); }
                                   100% { opacity: 0; transform: translate(calc(-50% + var(--scratch-shift,0px)), 60%) scaleY(0.4); } }
  @keyframes skill-claw-shard { 0% { opacity: 0; transform: translate(calc(-50% + var(--shard-drift,0px)), -30%) rotate(calc(var(--shard-rotate,0deg) - 24deg)) scale(0.45); }
                                 45% { opacity: 1; transform: translate(calc(-50% + var(--shard-drift,0px)), 18%) rotate(calc(var(--shard-rotate,0deg))) scale(1.05); }
                                 100% { opacity: 0; transform: translate(calc(-50% + var(--shard-drift,0px)), 70%) rotate(calc(var(--shard-rotate,0deg) + 14deg)) scale(0.6); } }
  @keyframes skill-claw-servo { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.35) rotate(0deg); }
                                 35% { opacity: 1; transform: translate(-50%, -50%) scale(1.0) rotate(40deg); }
                                 100% { opacity: 0; transform: translate(-50%, -50%) scale(1.25) rotate(90deg); } }
  @keyframes skill-claw-servo-flare { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.6); }
                                       40% { opacity: 0.85; transform: translate(-50%, -50%) scale(1.0); }
                                       100% { opacity: 0; transform: translate(-50%, -50%) scale(1.35); } }
  @keyframes skill-claw-mecha-spark { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(var(--spark-angle, 0deg)) translateX(0) scale(0.4); }
                                      40% { opacity: 1; }
                                      100% { opacity: 0; transform: translate(-50%, -50%) rotate(var(--spark-angle, 0deg)) translateX(92px) scale(0.7); } }
  @keyframes skill-beam-muzzle { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.25); }
                                 45% { opacity: 1; transform: translate(-50%, -50%) scale(1.0); }
                                 100% { opacity: 0; transform: translate(-50%, -50%) scale(1.25); } }
  @keyframes skill-beam-trail { 0% { opacity: 0; width: 0; }
                                30% { opacity: 1; width: var(--skill-length, 140px); }
                                100% { opacity: 0; width: var(--skill-length, 140px); } }
  @keyframes skill-beam-flare { 0% { opacity: 0; transform: translateY(-50%) scale(0.4); }
                                40% { opacity: 0.9; transform: translateY(-50%) scale(1.05); }
                                100% { opacity: 0; transform: translateY(-50%) scale(1.4); } }
  @keyframes skill-burst-ring { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.3); }
                                40% { opacity: 1; transform: translate(-50%, -50%) scale(1.0); }
                                100% { opacity: 0; transform: translate(-50%, -50%) scale(1.6); } }
  @keyframes skill-burst-wave { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.25); }
                                45% { opacity: 0.6; transform: translate(-50%, -50%) scale(1.05); }
                                100% { opacity: 0; transform: translate(-50%, -50%) scale(1.5); } }
  @keyframes skill-burst-core { 0% { opacity: 0.2; transform: translate(-50%, -50%) scale(0.8); }
                                40% { opacity: 1; transform: translate(-50%, -50%) scale(1.05); }
                                100% { opacity: 0; transform: translate(-50%, -50%) scale(1.2); } }
  @keyframes skill-aura-halo { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.5); }
                                35% { opacity: 1; transform: translate(-50%, -50%) scale(1.0); }
                                100% { opacity: 0; transform: translate(-50%, -50%) scale(1.35); } }
  @keyframes skill-aura-glyph { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.6); }
                                 35% { opacity: 1; transform: translate(-50%, -50%) scale(1.0); }
                                 100% { opacity: 0; transform: translate(-50%, -50%) scale(1.12); } }
  @keyframes skill-aura-pulse { 0% { opacity: 0.6; transform: scale(0.75); }
                                 60% { opacity: 0.8; transform: scale(1.0); }
                                 100% { opacity: 0; transform: scale(1.35); } }
  @keyframes skill-lightning-glow { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.35); }
                                    35% { opacity: 1; transform: translate(-50%, -50%) scale(1.05); }
                                    100% { opacity: 0; transform: translate(-50%, -50%) scale(1.4); } }
  @keyframes skill-lightning-bolt { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(calc(var(--skill-angle,0deg) - 12deg)) scaleY(0.2); }
                                   30% { opacity: 1; transform: translate(-50%, -50%) rotate(calc(var(--skill-angle,0deg) - 2deg)) scaleY(1.0); }
                                   100% { opacity: 0; transform: translate(-50%, -50%) rotate(calc(var(--skill-angle,0deg) + 12deg)) scaleY(0.4); } }
  @keyframes skill-rune-circle { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.4); }
                                 35% { opacity: 1; transform: translate(-50%, -50%) scale(1.0); }
                                 100% { opacity: 0; transform: translate(-50%, -50%) scale(1.2); } }
  @keyframes skill-rune-spin { 0% { opacity: 0.6; transform: translate(-50%, -50%) rotate(0deg) scale(0.95); }
                               100% { opacity: 0; transform: translate(-50%, -50%) rotate(220deg) scale(1.05); } }
  @keyframes skill-rune-flare { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.6); }
                                40% { opacity: 1; transform: translate(-50%, -50%) scale(1.0); }
                                100% { opacity: 0; transform: translate(-50%, -50%) scale(1.2); } }
  @keyframes skill-impact-shock { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.4); }
                                  40% { opacity: 1; transform: translate(-50%, -50%) scale(1.05); }
                                  100% { opacity: 0; transform: translate(-50%, -50%) scale(1.45); } }
  @keyframes skill-impact-dust { 0% { opacity: 0; transform: translate(-50%, -50%) scaleX(0.4); }
                                 40% { opacity: 0.75; transform: translate(-50%, -50%) scaleX(1.0); }
                                 100% { opacity: 0; transform: translate(-50%, -64%) scaleX(1.3); } }
  @keyframes skill-impact-crack { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.3); }
                                  30% { opacity: 0.9; transform: translate(-50%, -50%) scale(0.9); }
                                  100% { opacity: 0; transform: translate(-50%, -50%) scale(1.2); } }
  @keyframes skill-cascade-column { 0% { opacity: 0; height: 0; }
                                    30% { opacity: 0.75; height: 100%; }
                                    100% { opacity: 0; height: 100%; } }
  @keyframes skill-cascade-drop { 0% { opacity: 0; transform: translate(-50%, -30%) scale(0.6); }
                                   40% { opacity: 1; transform: translate(-50%, 20%) scale(1.0); }
                                   100% { opacity: 0; transform: translate(-50%, 80%) scale(0.4); } }
  @keyframes skill-spiral-spin { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.3) rotate(0deg); }
                                 40% { opacity: 1; transform: translate(-50%, -50%) scale(1.0) rotate(160deg); }
                                 100% { opacity: 0; transform: translate(-50%, -50%) scale(1.2) rotate(320deg); } }
  @keyframes skill-spiral-center { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.7); }
                                   40% { opacity: 1; transform: translate(-50%, -50%) scale(1.05); }
                                   100% { opacity: 0; transform: translate(-50%, -50%) scale(1.25); } }
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
  @keyframes fx-death-fade {
    0% { opacity: 1; }
    100% { opacity: 0; }
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
    color: rgba(255,255,255,0.45);
    cursor: not-allowed;
    box-shadow: none;
  }

  /* GOD'S WILL 菜单 */
  .gods-menu {
    position: absolute; z-index: 3002; background: rgba(20,20,30,0.95); color: #fff;
    border: 1px solid rgba(255,255,255,0.1); border-radius: 8px; padding: 8px; min-width: 180px;
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
    // Apply stun Buff instead of 1 layer
    const appliedStunDuration = Math.max(u.status.stunned || 0, KHATHIA_FATIGUE_STUN_DURATION);
    updateStatusStacks(u, 'stunned', appliedStunDuration, {label:'眩晕', type:'debuff'});
    appendLog(`${u.name} 因疲劳崩溃，陷入眩晕 Buff（${appliedStunDuration} 回合）`);
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
  if(!u || u.hp<=0 || amount<=0) return 0;
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
function adoraFieldMedic(u, aim){
  const t = getUnitAt(aim.r, aim.c);
  if(!t || t.side!==u.side){ appendLog('略懂的医术！ 目标无效'); return; }
  const healHp = 20;
  const healSp = 15;
  t.hp = Math.min(t.maxHp, t.hp + healHp);
  t.sp = Math.min(t.maxSp, t.sp + healSp);
  syncSpBroken(t);
  const currentStacks = (t.status && t.status.recoverStacks) ? t.status.recoverStacks : 0;
  updateStatusStacks(t,'recoverStacks', currentStacks + 1, {label:'恢复', type:'buff'});
  pulseCell(t.r, t.c);
  showGainFloat(t, healHp, healSp);
  showSkillFx('adora:略懂的医术！', {target:t});
  appendLog(`${u.name} 对 ${t.name} 使用 略懂的医术！：恢复 ${healHp} HP 和 ${healSp} SP，并赋予 1 层"恢复"`);
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
  applyStunOrStack(target, 1, {reason:'拉扯冲击'});
  const reduced = applySpDamage(target, 15, {sourceId: u.id});
  appendLog(`${target.name} SP -${reduced}`);
  u.dmgDone += dmg; unitActed(u);
}
function darioSweetAfterBitter(u){
  playerBonusStepsNextTurn += 4;
  appendLog(`${u.name} 使用 先苦后甜：下个玩家回合 +4 步`);
  showSkillFx('dario:先苦后甜',{target:u});
  unitActed(u);
}
function adoraDepend(u, aim){
  const t = getUnitAt(aim.r, aim.c);
  if(!t || t.side!==u.side){ appendLog('只能靠你了。。 目标无效'); return; }
  if(t.status.dependStacks>0){ appendLog(`${t.name} 已经处于“依赖”状态`); return; }
  damageUnit(u.id, 25, 0, `${u.name} 牺牲自身 25 HP`, null, {trueDamage:true, ignoreJixue:true, ignoreDepend:true, skillFx:'adora:只能靠你了。。', skillFxCtx:{target:u}});
  updateStatusStacks(t,'dependStacks',1,{label:'依赖', type:'buff'});
  pulseCell(t.r,t.c);
  showSkillFx('adora:只能靠你了。。',{target:t});
  appendLog(`${u.name} 对 ${t.name} 施加“依赖”：下一次攻击造成真实伤害并清空自身SP`);
  unitActed(u);
}
function karmaObeyMove(u, payload){
  const dest = payload && payload.moveTo; if(!dest){ appendLog('无效的目的地'); return; }
  cameraFocusOnCell(dest.r, dest.c); showTrail(u.r,u.c,dest.r,dest.c);
  if(dest.r !== u.r || dest.c !== u.c){
    const dir = cardinalDirFromDelta(dest.r - u.r, dest.c - u.c);
    setUnitFacing(u, dir);
  }
  u.r = dest.r; u.c = dest.c; pulseCell(u.r,u.c);
  showSkillFx('karma:都听你的',{target:u});
  registerUnitMove(u);
  if(u.consecAttacks > 0){ appendLog(`${u.name} 的连击被打断（移动）`); u.consecAttacks = 0; }
  u.sp = Math.min(u.maxSp, u.sp + 5); syncSpBroken(u); showGainFloat(u,0,5);
  unitActed(u);
}
function karmaGrip(u,target){
  if(!target || target.side===u.side){ appendLog('嗜血之握 目标无效'); return; }
  cameraFocusOnCell(target.r, target.c);
  let fixed = null;
  if(target.id==='khathia') fixed = 75;
  if(fixed!==null){
    const deal = Math.min(target.hp, fixed);
    damageUnit(target.id, deal, 0, `${u.name} 嗜血之握 重创 ${target.name}`, u.id, {ignoreToughBody:true, ignoreTuskWall:true, skillFx:'karma:嗜血之握'});
  } else {
    damageUnit(target.id, target.hp, 0, `${u.name} 嗜血之握 处决 ${target.name}`, u.id, {ignoreToughBody:true, skillFx:'karma:嗜血之握'});
  }
  unitActed(u);
}
function markKhathiaSkillUsed(u){
  if(!u) return;
  // Mark that Khathia has used a skill this turn (for movement restriction)
  if(u.id === 'khathia'){
    u._usedSkillThisTurn = true;
  }
}
function unitActed(u){
  if(!u) return;
  u.actionsThisTurn = Math.max(0, (u.actionsThisTurn||0)+1);

  let statusNeedsRefresh = false;
  let requireFullRender = false;

  if(u._jixueActivated){
    if(u.status){
      const prev = u.status.jixueStacks || 0;
      if(prev>0){
        updateStatusStacks(u,'jixueStacks', Math.max(0, prev - 1), {label:'鸡血', type:'buff'});
        appendLog(`${u.name} 的“鸡血”消散`);
        statusNeedsRefresh = true;
      }
    }
    u._jixueActivated = false;
  }

  if(u._dependUnleash){
    if(u.status){
      const prev = u.status.dependStacks || 0;
      if(prev>0){
        updateStatusStacks(u,'dependStacks', 0, {label:'依赖', type:'buff'});
        const beforeSp = u.sp;
        u.sp = 0;
        syncSpBroken(u);
        if(beforeSp>0){
          appendLog(`${u.name} 的“依赖”消散：SP 清空`);
          showDamageFloat(u,0,beforeSp);
        } else {
          appendLog(`${u.name} 的“依赖”消散：SP 已为 0`);
        }
        handleSpCrashIfNeeded(u);
        requireFullRender = true;
      }
    }
    u._dependUnleash = false;
  }

  if(requireFullRender){
    renderAll();
  } else if(statusNeedsRefresh){
    renderStatus();
  }
}
function karmaPunch(u,target){
  if(!target || target.side===u.side){ appendLog('沙包大的拳头 目标无效'); return; }
  const dmg = calcOutgoingDamage(u, 15, target, '沙包大的拳头');
  cameraFocusOnCell(target.r, target.c);
  damageUnit(target.id, dmg, 0, `${u.name} 出拳 ${target.name}`, u.id,{skillFx:'karma:沙包大的拳头'});
  u.dmgDone += dmg; u.consecAttacks = (u.consecAttacks||0)+1; unitActed(u);
}

// —— Khathia 技能 ——
function applyResentment(target, layers=1){
  if(!target || target.hp<=0) return 0;
  const stacks = addStatusStacks(target,'resentStacks', layers,{label:'怨念', type:'debuff'});
  appendLog(`${target.name} 怨念层数 -> ${stacks}`);
  return stacks;
}
function khathiaCollectTargets(cells){
  const set=new Set();
  const arr=[];
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !set.has(tu.id)){
      set.add(tu.id);
      arr.push(tu);
    }
  }
  return arr;
}
function rotateDirCounterClockwise(dir){
  switch(dir){
    case 'up': return 'left';
    case 'left': return 'down';
    case 'down': return 'right';
    case 'right': return 'up';
    default: return dir;
  }
}
async function khathia_FleshBlade(u, dir){
  markKhathiaSkillUsed(u);
  const area = forwardRect2x2(u, dir, 2, 1);
  if(area.length===0){ appendLog('血肉之刃：前方没有可以攻击的格子'); unitActed(u); return; }
  await telegraphThenImpact(area);
  const targets = khathiaCollectTargets(area);
  if(targets.length){ cameraFocusOnCell(targets[0].r, targets[0].c); }
  for(const target of targets){
    damageUnit(target.id,15,0,`${u.name} 血肉之刃·第一段 命中 ${target.name}`, u.id,{skillFx:'khathia:血肉之刃'});
    u.dmgDone += 15;
  }
  await stageMark(area);
  for(const target of targets){
    damageUnit(target.id,10,0,`${u.name} 血肉之刃·第二段 命中 ${target.name}`, u.id,{skillFx:'khathia:血肉之刃'});
    applyResentment(target,1);
    u.dmgDone += 10;
  }
  unitActed(u);
}
async function khathia_GrudgeClaw(u, dir){
  markKhathiaSkillUsed(u);
  const area = forwardRect2x2(u, dir, 2, 2);
  if(area.length===0){ appendLog('怨念之爪：前方没有可以抓取的目标'); unitActed(u); return; }
  await telegraphThenImpact(area);
  const targets = khathiaCollectTargets(area);
  if(targets.length){ cameraFocusOnCell(targets[0].r, targets[0].c); }
  for(const target of targets){
    damageUnit(target.id,10,15,`${u.name} 怨念之爪 撕裂 ${target.name}`, u.id,{skillFx:'khathia:怨念之爪'});
    applyResentment(target,1);
    u.dmgDone += 10;
  }
  unitActed(u);
}
async function khathia_BrutalSweep(u, dir){
  markKhathiaSkillUsed(u);
  const area = forwardRect2x2(u, dir, 4, 2);
  if(area.length===0){ appendLog('蛮横横扫：范围内没有敌人'); unitActed(u); return; }
  await telegraphThenImpact(area);
  const targets = khathiaCollectTargets(area);
  if(targets.length){ cameraFocusOnCell(targets[0].r, targets[0].c); }
  for(const target of targets){
    damageUnit(target.id,20,0,`${u.name} 蛮横横扫 命中 ${target.name}`, u.id,{skillFx:'khathia:蛮横横扫'});
    addStatusStacks(target,'paralyzed',1,{label:'恐惧', type:'debuff'});
    appendLog(`${target.name} 因恐惧下回合 -1 步`);
    u.dmgDone += 20;
  }
  unitActed(u);
}
async function khathia_Overwork(u, dir){
  markKhathiaSkillUsed(u);
  // Stage 1: 2x2 area, 2 steps forward
  const first = forwardRect2x2(u, dir, 2, 2);
  if(first.length===0){ appendLog('能者多劳：前方没有空间'); unitActed(u); return; }
  await telegraphThenImpact(first);
  const firstTargets = khathiaCollectTargets(first);
  if(firstTargets.length){ cameraFocusOnCell(firstTargets[0].r, firstTargets[0].c); }
  for(const target of firstTargets){
    damageUnit(target.id,10,15,`${u.name} 能者多劳·第一段 命中 ${target.name}`, u.id,{skillFx:'khathia:能者多劳'});
    u.dmgDone += 10;
  }
  await stageMark(first);
  
  // Stage 2: Same 2x2 area (attacks same cells again)
  const second = forwardRect2x2(u, dir, 2, 2);
  if(second.length>0){
    await telegraphThenImpact(second);
    const secondTargets = khathiaCollectTargets(second);
    if(secondTargets.length){ cameraFocusOnCell(secondTargets[0].r, secondTargets[0].c); }
    for(const target of secondTargets){
      damageUnit(target.id,15,10,`${u.name} 能者多劳·第二段 横切 ${target.name}`, u.id,{skillFx:'khathia:能者多劳'});
      applyResentment(target,1);
      u.dmgDone += 15;
    }
    await stageMark(second);
  }
  
  // Stage 3: Extended area from same position to map edge (width 2, depth to edge)
  // Calculate maximum depth based on direction and position
  // For 2x2 unit at (r,c), occupies rows r,r+1 and columns c,c+1
  let maxDepth = 2;
  if(dir === 'down'){
    maxDepth = ROWS - (u.r + 1); // From bottom edge (r+2) to map bottom (ROWS)
  } else if(dir === 'up'){
    maxDepth = u.r - 1; // From top edge (r-1) to map top (1)
  } else if(dir === 'left'){
    maxDepth = u.c - 1; // From left edge (c-1) to map left (1)
  } else if(dir === 'right'){
    maxDepth = COLS - (u.c + 1); // From right edge (c+2) to map right (COLS)
  }
  
  const third = forwardRect2x2(u, dir, 2, maxDepth);
  if(third.length>0){
    await telegraphThenImpact(third);
    const thirdTargets = khathiaCollectTargets(third);
    if(thirdTargets.length){ cameraFocusOnCell(thirdTargets[0].r, thirdTargets[0].c); }
    for(const target of thirdTargets){
      damageUnit(target.id,20,20,`${u.name} 能者多劳·终段 重砸 ${target.name}`, u.id,{skillFx:'khathia:能者多劳'});
      applyResentment(target,1);
      u.dmgDone += 20;
    }
  }
  unitActed(u);
}
async function khathia_AgonyRoar(u){
  markKhathiaSkillUsed(u);
  const before = u.sp;
  u.sp = u.maxSp;
  syncSpBroken(u);
  showGainFloat(u,0,u.sp-before);
  appendLog(`${u.name} 痛苦咆哮：SP 全面恢复`);
  const victims = Object.values(units).filter(t=> t.id!==u.id && t.hp>0 && (t.status?.resentStacks||0)>0);
  if(victims.length===0){
    appendLog('痛苦咆哮：场上没有怨念目标');
    unitActed(u);
    return;
  }
  for(const target of victims){
    const stacks = target.status.resentStacks || 0;
    updateStatusStacks(target,'resentStacks',0,{label:'怨念', type:'debuff'});
    const hpDmg = stacks * 5;
    const spDmg = stacks * 10;
    if(hpDmg>0 || spDmg>0){
      damageUnit(target.id,hpDmg,spDmg,`${u.name} 痛苦咆哮 撕裂 ${target.name}（怨念x${stacks}）`, u.id,{skillFx:'khathia:痛苦咆哮'});
    }
  }
  unitActed(u);
}
async function khathia_FinalStruggle(u){
  markKhathiaSkillUsed(u);
  const area = range_square_n(u,5);
  if(area.length===0){ unitActed(u); return; }
  await telegraphThenImpact(area);
  const targets = khathiaCollectTargets(area);
  if(targets.length){ cameraFocusOnCell(targets[0].r, targets[0].c); }
  for(const target of targets){
    damageUnit(target.id,50,70,`${u.name} 过多疲劳患者最终的挣扎 毁灭 ${target.name}`, u.id,{skillFx:'khathia:过多疲劳患者最终的挣扎'});
    u.dmgDone += 50;
  }
  unitActed(u);
}

// —— Khathia 防御姿态兼容（保留旧函数以支持玩家技能） ——
// —— 技能池/抽牌（含调整：Katz/Nelya/Kyn 技能）；移动卡统一蓝色 —— 
function skill(name,cost,color,desc,rangeFn,execFn,estimate={},meta={}){ return {name,cost,color,desc,rangeFn,execFn,estimate,meta}; }
function buildSkillFactoriesForUnit(u){
  const F=[];
  if(u.id==='adora'){
    F.push(
      { key:'短匕轻挥', prob:0.85, cond:()=>true, make:()=> skill('短匕轻挥',1,'green','邻格 10HP +5SP（背刺x1.5）',
        (uu,aimDir,aimCell)=> aimCell && mdist(uu,aimCell)===1? [{r:aimCell.r,c:aimCell.c,dir:cardinalDirFromDelta(aimCell.r-uu.r,aimCell.c-uu.c)}] : range_adjacent(uu),
        (uu,target)=> adoraDagger(uu,target),
        {},
        {castMs:900}
      )},
      { key:'枪击', prob:0.65, cond:()=>inventory.pistol, make:()=> skill('枪击',1,'green','指定方向整排 10HP+5SP（需手枪）',
        (uu,aimDir)=> aimDir? range_line(uu,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_line(uu,d).forEach(x=>a.push(x)); return a;})(),
        (uu,desc)=> playerGunExec(uu,desc),
        {aoe:true},
        {castMs:900}
      )},
      { key:'呀！你不要靠近我呀！！', prob:0.40, cond:()=>true, make:()=> skill('呀！你不要靠近我呀！！',2,'blue','位移≤5；若相邻敌人≤50%HP，追击一次短匕',
        (uu)=> range_move_radius(uu,5),
        (uu,payload)=> adoraPanicMove(uu,payload),
        {},
        {moveSkill:true, moveRadius:5, castMs:600}
      )},
      { key:'自制粉色迷你电击装置', prob:0.30, cond:()=>true, make:()=> skill('自制粉色迷你电击装置',3,'red','前方1-2格 10HP 15SP；叠1层眩晕；并使目标下回合-1步',
        (uu,aimDir)=> aimDir? range_forward_n(uu,2,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,2,d).forEach(x=>a.push(x)); return a;})(),
        (uu,target)=> adoraZap(uu,target),
        {},
        {castMs:1000}
      )}
    );
    F.push(
      { key:'略懂的医术！', prob:0.25, cond:()=>u.level>=25, make:()=> skill('略懂的医术！',2,'pink','以自身为中心5x5内选择友方：+20HP/+15SP，并赋予一层“恢复”Buff',
        (uu)=> range_square_n(uu,2).filter(p=>{ const tu=getUnitAt(p.r,p.c); return tu && tu.side===uu.side; }),
        (uu,aim)=> adoraFieldMedic(uu,aim),
        {aoe:false},
        {cellTargeting:true, castMs:900}
      )},
      { key:'加油哇！', prob:0.20, cond:()=>u.level>=25, make:()=> skill('加油哇！',4,'orange','以自身为中心5x5内选择友方：赋予 1 层“鸡血”（下一次攻击伤害翻倍，使用后移除）',
        (uu)=> range_square_n(uu,2).filter(p=>{ const tu=getUnitAt(p.r,p.c); return tu && tu.side===uu.side; }),
        (uu,aim)=> adoraCheer(uu,aim),
        {aoe:false},
        {cellTargeting:true, castMs:900}
      )},
      { key:'只能靠你了。。', prob:0.15, cond:()=>u.level>=35, make:()=> skill('只能靠你了。。',4,'orange','牺牲25HP；以自身为中心5格范围友方，赋予1层“依赖”（下一次攻击造成真实伤害并清空自身SP）',
        (uu)=> range_square_n(uu,5).filter(p=>{ const tu=getUnitAt(p.r,p.c); return tu && tu.side===uu.side; }),
        (uu,aim)=> adoraDepend(uu,aim),
        {aoe:false},
        {cellTargeting:true, castMs:900}
      )}
    );
  } else if(u.id==='dario'){
    F.push(
      { key:'机械爪击', prob:0.90, cond:()=>true, make:()=> skill('机械爪击',1,'green','前方1-2格 15HP',
        (uu,aimDir)=> aimDir? range_forward_n(uu,2,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,2,d).forEach(x=>a.push(x)); return a;})(),
        (uu,targetOrDesc)=> {
          if(targetOrDesc && targetOrDesc.id) darioClaw(uu,targetOrDesc);
          else if(targetOrDesc && targetOrDesc.dir){
            const line = range_forward_n(uu,2,targetOrDesc.dir);
            let tgt=null; for(const c of line){ const tu=getUnitAt(c.r,c.c); if(tu && tu.side!=='player'){ tgt=tu; break; } }
            if(tgt) darioClaw(uu,tgt); else appendLog('机械爪击 未命中');
          }
        },
        {},
        {castMs:900}
      )},
      { key:'枪击', prob:0.65, cond:()=>inventory.pistol, make:()=> skill('枪击',1,'green','指定方向整排 10HP+5SP（需手枪）',
        (uu,aimDir)=> aimDir? range_line(uu,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_line(uu,d).forEach(x=>a.push(x)); return a;})(),
        (uu,desc)=> playerGunExec(uu,desc),
        {aoe:true},
        {castMs:900}
      )},
      { key:'迅捷步伐', prob:0.40, cond:()=>true, make:()=> skill('迅捷步伐',2,'blue','位移≤4；最近敌人 SP -5',
        (uu)=> range_move_radius(uu,4),
        (uu,payload)=> darioSwiftMove(uu,payload),
        {},
        {moveSkill:true, moveRadius:4, castMs:600}
      )},
      { key:'拿来吧你！', prob:0.30, cond:()=>true, make:()=> skill('拿来吧你！',3,'red','方向整排：拉至最近空格 +20HP、叠层、-15SP（小Boss/Boss免疫拉扯）',
        (uu,aimDir)=> aimDir? range_line(uu,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_line(uu,d).forEach(x=>a.push(x)); return a;})(),
        (uu,desc)=> darioPull(uu,desc),
        {aoe:true},
        {castMs:1100}
      )}
    );
    F.push(
      { key:'先苦后甜', prob:0.15, cond:()=>u.level>=25 && ((u.skillPool||[]).filter(s=>s && s.name==='先苦后甜').length < 2), make:()=> skill('先苦后甜',4,'orange','自我激励：下个玩家回合额外 +4 步（技能池最多保留2张）',
        (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
        (uu)=> darioSweetAfterBitter(uu),
        {},
        {castMs:700}
      )}
    );
  } else if(u.id==='karma'){
    F.push(
      { key:'沙包大的拳头', prob:0.90, cond:()=>true, make:()=> skill('沙包大的拳头',1,'green','邻格 15HP（连击递增）',
        (uu,aimDir,aimCell)=> aimCell && mdist(uu,aimCell)===1? [{r:aimCell.r,c:aimCell.c,dir:cardinalDirFromDelta(aimCell.r-uu.r,aimCell.c-uu.c)}] : range_adjacent(uu),
        (uu,target)=> karmaPunch(uu,target),
        {},
        {castMs:900}
      )},
      { key:'枪击', prob:0.65, cond:()=>inventory.pistol, make:()=> skill('枪击',1,'green','指定方向整排 10HP+5SP（需手枪）',
        (uu,aimDir)=> aimDir? range_line(uu,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_line(uu,d).forEach(x=>a.push(x)); return a;})(),
        (uu,desc)=> playerGunExec(uu,desc),
        {aoe:true},
        {castMs:900}
      )},
      { key:'都听你的', prob:0.40, cond:()=>true, make:()=> skill('都听你的',2,'blue','位移≤3，并恢复自身 5SP（打断连击）',
        (uu)=> range_move_radius(uu,3),
        (uu,payload)=> karmaObeyMove(uu,payload),
        {},
        {moveSkill:true, moveRadius:3, castMs:600}
      )},
      { key:'嗜血之握', prob:0.30, cond:()=>true, make:()=> {
          const sk = skill('嗜血之握',3,'red','（需连击≥4）精英100/小Boss80/Boss75/普通处决',
            (uu,aimDir)=> aimDir? range_forward_n(uu,2,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,2,d).forEach(x=>a.push(x)); return a;})(),
            (uu,target)=> karmaGrip(uu,target),
            {},
            {requireConsec:4, castMs:900}
          );
          return sk;
        }
      }
    );
    F.push(
      { key:'深呼吸', prob:0.20, cond:()=>u.level>=25 && !(u.skillPool||[]).some(s=>s.name==='深呼吸'), make:()=> skill('深呼吸',2,'white','被动：只要此卡在技能池，伤害+10%；主动使用：自身SP回满并+10HP（使用后该卡被移除）',
        (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
        (uu)=> karmaDeepBreath(uu),
        {},
        {castMs:700}
      )}
    );
  } else if(u.id==='khathia'){
    F.push(
      { key:'血肉之刃', prob:0.70, cond:()=>true, make:()=> skill('血肉之刃',1,'green','前方2x1：15HP+10HP，多段叠怨念',
        (uu,aimDir)=> { const dir=aimDir||uu.facing; return forwardRect2x2(uu,dir,2,1).map(c=>({...c,dir})); },
        async (uu,desc)=> { const dir = desc && desc.dir ? desc.dir : uu.facing; await khathia_FleshBlade(uu, dir); },
        {},
        {castMs:1100}
      )},
      { key:'怨念之爪', prob:0.70, cond:()=>true, make:()=> skill('怨念之爪',1,'green','前方2x2：10HP+15SP并叠怨念',
        (uu,aimDir)=> { const dir=aimDir||uu.facing; return forwardRect2x2(uu,dir,2,2).map(c=>({...c,dir})); },
        async (uu,desc)=> { const dir = desc && desc.dir ? desc.dir : uu.facing; await khathia_GrudgeClaw(uu, dir); },
        {},
        {castMs:1100}
      )},
      { key:'蛮横横扫', prob:0.60, cond:()=>true, make:()=> skill('蛮横横扫',2,'red','前方4x2：20HP并附恐惧',
        (uu,aimDir)=> { const dir=aimDir||uu.facing; return forwardRect2x2(uu,dir,4,2).map(c=>({...c,dir})); },
        async (uu,desc)=> { const dir = desc && desc.dir ? desc.dir : uu.facing; await khathia_BrutalSweep(uu, dir); },
        {aoe:true},
        {castMs:1400}
      )},
      { key:'能者多劳', prob:0.45, cond:()=>true, make:()=> skill('能者多劳',2,'red','多段：前2x2→同区→至边缘，叠怨念并削SP',
        (uu,aimDir)=> { 
          const dir=aimDir||uu.facing; 
          // Show the maximum range (stage 3) for targeting
          // For 2x2 unit, calculate depth to map edge in attack direction
          let maxDepth = 2;
          if(dir === 'down'){ maxDepth = ROWS - (uu.r + 1); }
          else if(dir === 'up'){ maxDepth = uu.r - 1; }
          else if(dir === 'left'){ maxDepth = uu.c - 1; }
          else if(dir === 'right'){ maxDepth = COLS - (uu.c + 1); }
          return forwardRect2x2(uu,dir,2,maxDepth).map(c=>({...c,dir})); 
        },
        async (uu,desc)=> { const dir = desc && desc.dir ? desc.dir : uu.facing; await khathia_Overwork(uu, dir); },
        {aoe:true},
        {castMs:1900}
      )},
      { key:'痛苦咆哮', prob:0.35, cond:()=>true, make:()=> skill('痛苦咆哮',2,'red','恢复自身SP并清算所有怨念目标',
        (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
        async (uu)=> await khathia_AgonyRoar(uu),
        {},
        {castMs:1500}
      )},
      { key:'过多疲劳患者最终的挣扎', prob:0.30, cond:()=>true, make:()=> skill('过多疲劳患者最终的挣扎',3,'red','以自身为中心大范围：50HP+70SP',
        (uu)=> range_square_n(uu,5).map(c=>({...c,dir:uu.facing})),
        async (uu)=> await khathia_FinalStruggle(uu),
        {aoe:true},
        {castMs:2200}
      )}
    );
  }
  return F;
}
function drawOneSkill(u){
  const fset = buildSkillFactoriesForUnit(u);
  const viable = fset.filter(f=>f.cond());
  if(viable.length===0) return null;
  for(let i=0;i<30;i++){ const f=viable[Math.floor(Math.random()*viable.length)]; if(Math.random()<f.prob) return f.make(); }
  viable.sort((a,b)=> b.prob-a.prob);
  return viable[0].make();
}
function drawSkills(u, n){
  let toDraw = Math.max(0, Math.min(n, SKILLPOOL_MAX - u.skillPool.length));
  while(toDraw>0){ const sk=drawOneSkill(u); if(!sk) break; u.skillPool.push(sk); toDraw--; }
  if(u.skillPool.length > SKILLPOOL_MAX) u.skillPool.length = SKILLPOOL_MAX;
}
function ensureStartHand(u){ if(u.dealtStart) return; u.skillPool.length = 0; drawSkills(u, START_HAND_COUNT); u.dealtStart = true; appendLog(`${u.name} 起手手牌：${u.skillPool.map(s=>s.name).join(' / ')}`); }

// —— GOD’S WILL —— 
function disarmGodsWill(){
  godsWillArmed = false;
  if(godsWillBtn) godsWillBtn.classList.remove('armed');
  if(godsWillMenuEl){ godsWillMenuEl.remove(); godsWillMenuEl = null; }
  appendLog('GOD’S WILL：退出选取模式');
}
function showGodsWillMenuAtUnit(u){
  if(!battleAreaEl || !u || u.hp<=0){ appendLog('GOD’S WILL：目标无效或已倒下'); disarmGodsWill(); return; }
  if(godsWillMenuEl){ godsWillMenuEl.remove(); godsWillMenuEl=null; }
  const p = getCellCenter(u.r, u.c);
  const areaRect = battleAreaEl.getBoundingClientRect();
  godsWillMenuEl = document.createElement('div');
  godsWillMenuEl.className = 'gods-menu';
  godsWillMenuEl.style.left = `${Math.max(8, p.x + areaRect.left + 8)}px`;
  godsWillMenuEl.style.top  = `${Math.max(8, p.y + areaRect.top  - 8)}px`;
  godsWillMenuEl.innerHTML = `
    <div class="title">GOD’S WILL → ${u.name}</div>
    <div class="row">
      <button class="kill">杀死</button>
      <button class="onehp">留 1 HP</button>
      <button class="cancel">取消</button>
    </div>
  `;
  godsWillMenuEl.querySelector('.kill').onclick = (e)=>{
    e.stopPropagation();
    const before = u.hp;
    u.hp = 0;
    appendLog(`GOD’S WILL：${u.name} 被直接抹除（-${before} HP）`);
    cameraShake('heavy');
    showAttackFx({target: u, trueDamage: true, heavy: true});
    showDamageFloat(u,before,0);
    if(before>0){ showDeathFx(u); }
    renderAll();
    disarmGodsWill();
  };
  godsWillMenuEl.querySelector('.onehp').onclick = (e)=>{
    e.stopPropagation();
    if(u.hp>1){
      const delta = u.hp - 1;
      u.hp = 1;
      appendLog(`GOD’S WILL：${u.name} 被压到 1 HP（-${delta} HP）`);
      const heavy = delta >= Math.max(18, Math.round(u.maxHp * 0.3));
      cameraShake(heavy ? 'heavy' : 'normal');
      showAttackFx({target: u, heavy, trueDamage: true});
      showDamageFloat(u,delta,0);
    } else {
      appendLog(`GOD’S WILL：${u.name} 已是 1 HP`);
    }
    renderAll();
    disarmGodsWill();
  };
  godsWillMenuEl.querySelector('.cancel').onclick = (e)=>{ e.stopPropagation(); disarmGodsWill(); };
  document.body.appendChild(godsWillMenuEl);
}
function toggleGodsWill(){
  godsWillArmed = !godsWillArmed;
  if(godsWillBtn){
    if(godsWillArmed){
      godsWillBtn.classList.add('armed');
      appendLog('GOD’S WILL：已开启，点击任意单位选择“杀死/留 1 HP”，ESC 可取消');
    } else {
      godsWillBtn.classList.remove('armed');
      appendLog('GOD’S WILL：关闭');
    }
  }
  if(!godsWillArmed && godsWillMenuEl){ godsWillMenuEl.remove(); godsWillMenuEl=null; }
}
// 全屏切换（原生优先，失败时启用模拟全屏）
function setSimFullscreen(on){
  isSimFullscreen = !!on;
  document.documentElement.classList.toggle('fs-sim', on);
  document.body.classList.toggle('fs-sim', on);
  if(fsBtn){
    fsBtn.classList.toggle('on', on || !!document.fullscreenElement);
    fsBtn.textContent = (on || document.fullscreenElement) ? 'Exit Full Screen' : 'Full Screen';
  }
  // 刷新覆盖
  setTimeout(()=> refreshLargeOverlays(), 80);
}
function toggleFullscreen(){
  if(document.fullscreenElement){
    document.exitFullscreen().finally(()=> setSimFullscreen(false));
    return;
  }
  if(document.documentElement.requestFullscreen){
    document.documentElement.requestFullscreen().then(()=>{
      setSimFullscreen(false);
    }).catch(()=>{
      setSimFullscreen(!isSimFullscreen);
    });
  } else {
    setSimFullscreen(!isSimFullscreen);
  }
}
document.addEventListener('fullscreenchange', ()=>{
  if(fsBtn){
    fsBtn.classList.toggle('on', !!document.fullscreenElement);
    fsBtn.textContent = document.fullscreenElement ? 'Exit Full Screen' : 'Full Screen';
  }
  setTimeout(()=> refreshLargeOverlays(), 80);
});

// —— UI/交互 —— 
function buildGrid(){
  if(!battleAreaEl) return;
  // 确保 --cell 可用，避免“无角色/看不到格子”
  battleAreaEl.style.setProperty('--cell', `${CELL_SIZE}px`);
  battleAreaEl.style.gridTemplateColumns = `repeat(${COLS}, var(--cell))`;
  battleAreaEl.style.gridTemplateRows = `repeat(${ROWS}, var(--cell))`;
  const preservedFxLayer = fxLayer;
  battleAreaEl.innerHTML = '';
  for(let r=1;r<=ROWS;r++){
    for(let c=1;c<=COLS;c++){
      const cell = document.createElement('div');
      cell.className = 'cell';
      if(isVoidCell(r,c)) cell.classList.add('void');
      if(isCoverCell(r,c)) cell.classList.add('cover');
      cell.dataset.r=r; cell.dataset.c=c;
      const coord=document.createElement('div'); coord.className='coord'; coord.textContent=`${r},${c}`; cell.appendChild(coord);

      cell.addEventListener('click', ()=>{
        if(interactionLocked) return;
        const rr=+cell.dataset.r, cc=+cell.dataset.c;
        if(_skillSelection){
          handleSkillConfirmCell(_skillSelection.unit,_skillSelection.skill,{r:rr,c:cc});
          return;
        }
        const occ = getUnitAt(rr,cc);
        if(occ){
          if(godsWillArmed){ showGodsWillMenuAtUnit(occ); return; }
          onUnitClick(occ.id); return;
        }
        onCellClick(rr,cc);
      });
      cell.addEventListener('mouseenter', ()=>{
        if(interactionLocked) return;
        if(_skillSelection){
          const rr=+cell.dataset.r, cc=+cell.dataset.c;
          handleSkillPreviewCell(_skillSelection.unit,_skillSelection.skill,{r:rr,c:cc});
        }
      });
      cell.addEventListener('contextmenu', (e)=>{ e.preventDefault(); if(interactionLocked) return; clearSkillAiming(); renderAll(); });
      battleAreaEl.appendChild(cell);
    }
  }
  if(preservedFxLayer){
    battleAreaEl.appendChild(preservedFxLayer);
  }
}
function refreshLargeOverlays(){
  if(!battleAreaEl) return;
  battleAreaEl.querySelectorAll('.largeOverlay').forEach(n=>n.remove());
  for(const id in units){
    const u=units[id];
    if(u && u.hp>0 && u.size===2){
      renderLargeUnitOverlay(u);
    }
  }
}
function getSpBarDisplay(u){
  // For units with negative SP (like Khathia with spFloor=-100):
  // SP from 0 to -100 displays as purple bar filling from 0% to 100%
  if(u.sp < 0 && u.spFloor < 0){
    const spPct = Math.max(0, Math.min(100, Math.abs(u.sp / u.spFloor) * 100));
    const color = '#9254de'; // Purple color for negative SP
    return { spPct, color };
  }
  // Normal positive SP display
  const spPct = Math.max(0, Math.min(100, (u.maxSp ? (u.sp/u.maxSp*100) : 0)));
  const color = '#40a9ff'; // Blue color for positive SP
  return { spPct, color };
}
function placeUnits(){
  if(!battleAreaEl) return;
  document.querySelectorAll('.cell .unit').forEach(n=>n.remove());
  battleAreaEl.querySelectorAll('.largeOverlay').forEach(n=>n.remove());

  for(const id in units){
    const u=units[id]; if(u.hp<=0) continue;

    if(u.size===2){
      renderLargeUnitOverlay(u);
      continue;
    }

    const sel=`.cell[data-r="${u.r}"][data-c="${u.c}"]`;    const cell=document.querySelector(sel);
    if(!cell) continue;
    const div=document.createElement('div');
    div.className='unit ' + (u.side==='player'?'player':'enemy');
    div.dataset.id=id;
    div.dataset.facing = u.facing || 'right';

    div.addEventListener('click',(e)=>{
      if(interactionLocked) return;
      if(godsWillArmed){
        e.stopPropagation();
        showGodsWillMenuAtUnit(u);
        return;
      }
      if(_skillSelection){
        e.stopPropagation();
        handleSkillConfirmCell(_skillSelection.unit,_skillSelection.skill,{r:u.r,c:u.c});
        return;
      }
      e.stopPropagation();
      onUnitClick(id);
    });

    const hpPct = Math.max(0, Math.min(100, (u.hp/u.maxHp*100)||0));
    const spDisplay = getSpBarDisplay(u);
    div.innerHTML = `
      <div>${u.name}</div>
      <div class="hpbar"><div class="hpfill" style="width:${hpPct}%"></div></div>
      <div class="spbar"><div class="spfill" style="width:${spDisplay.spPct}%; background:${spDisplay.color}"></div></div>
    `;
    const facingArrow=document.createElement('div');
    facingArrow.className='facing-arrow';
    div.appendChild(facingArrow);
    cell.appendChild(div);
  }
}

//part 1 结束
function renderLargeUnitOverlay(u){
  // Pixel-perfect 2x2 overlay using actual cell offsets to avoid rounding drift
  const tl = getCellEl(u.r, u.c);
  const br = getCellEl(u.r+1, u.c+1);
  if(!tl || !br || !battleAreaEl) return;

  const left   = tl.offsetLeft;
  const top    = tl.offsetTop;
  const right  = br.offsetLeft + br.offsetWidth;
  const bottom = br.offsetTop  + br.offsetHeight;
  const width  = right - left;
  const height = bottom - top;

  const overlay = document.createElement('div');
  overlay.className = 'largeOverlay ' + (u.side==='player'?'player':'enemy');
  overlay.dataset.facing = u.facing || 'right';
  overlay.style.position = 'absolute';
  overlay.style.left = left + 'px';
  overlay.style.top  = top  + 'px';
  overlay.style.width  = width  + 'px';
  overlay.style.height = height + 'px';
  overlay.style.background = 'rgba(255,77,79,0.08)';
  overlay.style.border = '1px solid rgba(255,77,79,0.35)';
  overlay.style.borderRadius = '10px';
  overlay.style.color = '#e9eefc';
  overlay.style.display = 'grid';
  overlay.style.gridTemplateRows = 'auto auto auto';
  overlay.style.placeItems = 'center';
  overlay.style.padding = '6px 8px';
  overlay.style.pointerEvents = 'auto';

  overlay.addEventListener('click', (e)=>{
    if(interactionLocked) return;
    if(_skillSelection){
      const attacker = _skillSelection.unit;
      const skill = _skillSelection.skill;
      const aim = chooseBestAimCellForLargeTarget(attacker, skill, u) || {r:u.r, c:u.c};
      handleSkillConfirmCell(attacker, skill, aim);
      return;
    }
    onUnitClick(u.id);
  });

  const hpPct = Math.max(0, Math.min(100, (u.hp/u.maxHp*100)||0));
  const spDisplay = getSpBarDisplay(u);

  overlay.innerHTML = `
    <div class="title">${u.name}</div>
    <div class="hpbar"><div class="hpfill" style="width:${hpPct}%"></div></div>
    <div class="spbar"><div class="spfill" style="width:${spDisplay.spPct}%; background:${spDisplay.color}"></div></div>
  `;
  const facingArrow=document.createElement('div');
  facingArrow.className='facing-arrow';
  overlay.appendChild(facingArrow);

  battleAreaEl.appendChild(overlay);
}

// —— 大体型（2x2）瞄准辅助 —— 
function getCoveredCells(u){
  if(!u || u.hp<=0) return [];
  if(u.size===2) return [{r:u.r,c:u.c},{r:u.r+1,c:u.c},{r:u.r,c:u.c+1},{r:u.r+1,c:u.c+1}];
  return [{r:u.r,c:u.c}];
}
function chooseBestAimCellForLargeTarget(attacker, sk, target){
  if(!attacker || !sk || !target) return null;
  const cells = getCoveredCells(target);
  // 优先：在技能范围内且与攻击者最近的覆盖格
  let best=null, bestD=1e9;
  for(const c of cells){
    const dir = resolveAimDirForSkill(attacker, sk, c);
    let inRange=false;
    try{
      const rc = sk.rangeFn(attacker, dir, c) || [];
      inRange = rangeIncludeCell(rc, c);
    }catch(e){ inRange=false; }
    if(inRange){
      const d = mdist(attacker, c);
      if(d < bestD){ bestD=d; best=c; }
    }
  }
  if(best) return best;
  // 兜底：返回最近覆盖格
  let nearest=cells[0], nd=mdist(attacker, cells[0]);
  for(const c of cells){ const d=mdist(attacker,c); if(d<nd){ nd=d; nearest=c; } }
  return nearest;
}

function summarizeNegatives(u){
  let parts=[];
  if(u._staggerStacks && (u.stunThreshold||1)>1) parts.push(`叠层${u._staggerStacks}/${u.stunThreshold}`);
  if(u.status.stunned>0) parts.push(`眩晕x${u.status.stunned}`);
  if(u.status.paralyzed>0) parts.push(`恐惧x${u.status.paralyzed}`);
  if(u.status.bleed>0) parts.push(`流血x${u.status.bleed}`);
  if(u.status.recoverStacks>0) parts.push(`恢复x${u.status.recoverStacks}`);
  if(u.status.jixueStacks>0) parts.push(`鸡血x${u.status.jixueStacks}`);
  if(u.status.dependStacks>0) parts.push(`依赖x${u.status.dependStacks}`);
  if(u.status.resentStacks>0) parts.push(`怨念x${u.status.resentStacks}`);
  if(u._spBroken) parts.push(`SP崩溃`);
  if(u._spCrashVuln) parts.push('SP崩溃易伤');
  if(u._stanceType && u._stanceTurns>0){
    parts.push(u._stanceType==='defense' ? `防御姿态(${u._stanceTurns})` : `反伤姿态(${u._stanceTurns})`);
  }
  return parts.join(' ');
}
function renderStatus(){
  if(!partyStatus) return;
  partyStatus.innerHTML='';
  for(const id of ['adora','dario','karma']){
    const u=units[id]; if(!u) continue;
    const el=document.createElement('div'); el.className='partyRow';
    el.innerHTML=`<strong>${u.name}</strong> HP:${u.hp}/${u.maxHp} SP:${u.sp}/${u.maxSp} ${summarizeNegatives(u)}`;
    partyStatus.appendChild(el);
  }
  const enemyWrap=document.createElement('div'); enemyWrap.style.marginTop='10px'; enemyWrap.innerHTML='<strong>敌方（疲惫的极限）</strong>';
  const enemyUnits = Object.values(units).filter(u=>u.side==='enemy' && u.hp>0);
  for(const u of enemyUnits){
    const el=document.createElement('div'); el.className='partyRow small';
    el.innerHTML=`${u.name} HP:${u.hp}/${u.maxHp} SP:${u.sp}/${u.maxSp} ${u.oppression?'[压迫] ':''}${u._comeback?'[力挽狂澜] ':''}${summarizeNegatives(u)}`;
    enemyWrap.appendChild(el);
  }
  partyStatus.appendChild(enemyWrap);
}
function updateStepsUI(){
  if(playerStepsEl) playerStepsEl.textContent=playerSteps;
  if(enemyStepsEl) enemyStepsEl.textContent=enemySteps;
  if(roundCountEl) roundCountEl.textContent = String(roundsPassed);
}

// —— 选中/瞄准 —— 
function canUnitMove(u){
  if(!u) return false;
  if(u._stanceType && u._stanceTurns>0) return false; // 姿态期间禁止移动
  if(typeof u.maxMovePerTurn === 'number' && u.maxMovePerTurn >= 0){
    if((u.stepsMovedThisTurn||0) >= u.maxMovePerTurn) return false;
  }
  return true;
}
function clearSkillAiming(){ _skillSelection=null; clearHighlights(); }
function clearAllSelection(){ _skillSelection=null; selectedUnitId=null; clearHighlights(); if(skillPool) skillPool.innerHTML=''; if(selectedInfo) selectedInfo.innerHTML=''; }
function startSkillAiming(u,sk){
  if(interactionLocked || !u || u.hp<=0) return;
  clearHighlights();
  _skillSelection={unit:u,skill:sk};
  appendLog(`${u.name} 选择了技能：${sk.name}，移动鼠标到目标格以预览并点击`);
  handleSkillPreviewCell(u,sk,{r:u.r,c:u.c});
}
function rangeIncludeCell(cells, aimCell){ return cells.some(c=>c.r===aimCell.r && c.c===aimCell.c); }
function resolveAimDirForSkill(u, sk, aimCell){
  const vecDir = cardinalDirFromDelta(aimCell.r - u.r, aimCell.c - u.c);
  try{
    const cells = sk.rangeFn(u, vecDir, aimCell) || [];
    if(rangeIncludeCell(cells, aimCell)) return vecDir;
  }catch(e){}
  for(const dir of Object.keys(DIRS)){
    let cells=[];
    try{ cells = sk.rangeFn(u, dir, aimCell) || []; }catch(e){ cells=[]; }
    if(rangeIncludeCell(cells, aimCell)) return dir;
  }
  return vecDir;
}
function handleSkillPreviewCell(u, sk, aimCell){
  if(interactionLocked || !u || u.hp<=0) return;
  clearHighlights();
  const aimDir = resolveAimDirForSkill(u, sk, aimCell);
  const cells = sk.rangeFn(u, aimDir, aimCell) || [];
  for(const c of cells) markCell(c.r,c.c,'skill');
  const inPreview = rangeIncludeCell(cells, aimCell);
  if(inPreview) markCell(aimCell.r, aimCell.c, 'target');
}
function consumeCardFromHand(u, sk){ if(!u || !u.skillPool) return; const idx=u.skillPool.indexOf(sk); if(idx>=0) u.skillPool.splice(idx,1); }
function discardSkill(u, sk){
  if(interactionLocked) return;
  if(!u || !sk) return;
  if(u.side !== currentSide){ appendLog('现在不是你的回合'); return; }
  if(u.hp<=0){ appendLog('该单位已无法行动'); return; }
  if(_skillSelection && _skillSelection.unit===u && _skillSelection.skill===sk){ clearSkillAiming(); }
  consumeCardFromHand(u, sk);
  appendLog(`${u.name} 弃置了技能：${sk.name}`);
  renderAll(); showSelected(u);
}
async function handleSkillConfirmCell(u, sk, aimCell){
  if(interactionLocked || !u || u.hp<=0) return;
  if(!_skillSelection) return;

  if(sk.meta && sk.meta.moveSkill && !canUnitMove(u)){
    appendLog(`${u.name} 处于姿态中，无法进行任何移动`);
    clearSkillAiming(); renderAll(); return;
  }

  if(sk.meta && sk.meta.requireConsec && (u.consecAttacks||0) < sk.meta.requireConsec){
    appendLog(`未满足使用条件：需要当前连击 ≥ ${sk.meta.requireConsec}`);
    clearSkillAiming(); renderAll(); return;
  }

  const currentSteps = (u.side==='player')? playerSteps : enemySteps;
  if(sk.cost > currentSteps){ appendLog('步数不足'); clearSkillAiming(); renderAll(); return; }

  const aimDir = resolveAimDirForSkill(u, sk, aimCell);
  const cells = sk.rangeFn(u, aimDir, aimCell) || [];
  if(!rangeIncludeCell(cells, aimCell)){ appendLog('该格不在技能范围内'); return; }

  if(u.side==='player'){ playerSteps = Math.max(0, playerSteps - sk.cost); } else { enemySteps = Math.max(0, enemySteps - sk.cost); }

  if(aimDir && (aimCell.r !== u.r || aimCell.c !== u.c)){
    setUnitFacing(u, aimDir);
  }

  const targetUnit = getUnitAt(aimCell.r, aimCell.c);
  
  try{
    let result;
    if(sk.meta && sk.meta.moveSkill) result = sk.execFn(u, {moveTo: aimCell});
    else if(sk.meta && sk.meta.cellTargeting) result = sk.execFn(u, aimCell);
    else if(sk.estimate && sk.estimate.aoe) result = sk.execFn(u, {dir:aimDir});
    else if(targetUnit) result = sk.execFn(u, targetUnit);
    else result = sk.execFn(u, {r:aimCell.r,c:aimCell.c,dir:aimDir});
    
    // Lock interactions for async multi-stage attacks
    if(result instanceof Promise){
      setInteractionLocked(true);
      await result;
      setInteractionLocked(false);
    }
  }catch(e){ 
    setInteractionLocked(false); // Ensure unlock on error
    console.error('技能执行错误',e); 
    appendLog(`[错误] 技能执行失败：${sk.name} - ${e.message}`); 
  }

  consumeCardFromHand(u, sk);
  clearSkillAiming();
  renderAll();
  showSelected(u);

  if(u.id==='karma' && sk.name!=='沙包大的拳头'){
    if(u.consecAttacks>0) appendLog(`${u.name} 的连击被打断（使用其他技能）`);
    u.consecAttacks = 0;
  }

  unitActed(u);
  setTimeout(()=>{ checkEndOfTurn(); }, 220);
}
function onUnitClick(id){
  if(interactionLocked) return;
  const u=units[id]; if(!u) return;
  if(godsWillArmed){ showGodsWillMenuAtUnit(u); return; }
  if(u.side==='enemy' && ENEMY_IS_AI_CONTROLLED){ appendLog('敌方单位由 AI 控制，无法手动操作'); selectedUnitId=id; showSelected(u); return; }
  if(u.side===currentSide && u.status.stunned) appendLog(`${u.name} 眩晕中，无法行动`);
  selectedUnitId=id; showSelected(u);
}
function onCellClick(r,c){
  if(interactionLocked) return;
  if(_skillSelection) return;
  if(!selectedUnitId) {
    if(godsWillArmed){ appendLog('GOD’S WILL：请直接点击单位，而非空格'); }
    return;
  }
  const sel=units[selectedUnitId]; if(!sel || sel.hp<=0) return;

  if(sel.side==='enemy' && ENEMY_IS_AI_CONTROLLED){ appendLog('敌方单位由 AI 控制'); return; }
  if(sel.side!==currentSide){ appendLog('不是该单位的回合'); return; }
  if(sel.status.stunned){ appendLog(`${sel.name} 眩晕中，无法行动`); return; }
  if(!canUnitMove(sel)){ appendLog(`${sel.name} 处于${sel._stanceType==='defense'?'防御姿态':'反伤姿态'}，本回合不能移动`); return; }
  // Khathia restriction: cannot move after casting a skill
  if(sel.id === 'khathia' && sel._usedSkillThisTurn){ 
    appendLog(`${sel.name} 已施放技能，本回合不能再移动`); 
    return; 
  }

  const key=`${r},${c}`; if(!highlighted.has(key)) return;
  if(playerSteps<=0 && sel.side==='player'){ appendLog('剩余步数不足'); return; }
  const occ=getUnitAt(r,c); if(occ){ appendLog('格子被占用'); return; }

  if(sel.size===2){ if(!canPlace2x2(sel, r, c)){ appendLog('该位置无法容纳 2x2 单位'); return; } }

  const moveDir = cardinalDirFromDelta(r - sel.r, c - sel.c);
  setUnitFacing(sel, moveDir);
  sel.r=r; sel.c=c;
  registerUnitMove(sel);
  if(sel.side==='player') playerSteps=Math.max(0, playerSteps-1); else enemySteps=Math.max(0, enemySteps-1);
  appendLog(`${sel.name} 移动到 (${r},${c})`);
  if(sel.side!=='player') cameraFocusOnCell(r,c);
  pulseCell(r,c);
  if(sel.id==='karma' && sel.consecAttacks>0){ appendLog(`${sel.name} 的连击被打断（移动）`); sel.consecAttacks=0; }
  unitActed(sel);
  clearHighlights(); renderAll(); showSelected(sel);
  setTimeout(()=>{ checkEndOfTurn(); }, 160);
}
function showSelected(u){
  clearSkillAiming();
  const base=`<strong>${u.name}</strong><br>HP: ${u.hp}/${u.maxHp} SP:${u.sp}/${u.maxSp} 级别:${u.level} ${summarizeNegatives(u)}`;
  let extra='';
  if(u.skillPool && u.skillPool.length){ extra += `<div class="partyRow small">手牌(${u.skillPool.length}/${SKILLPOOL_MAX}): ${u.skillPool.map(s=>s.name).join(' / ')}</div>`; }
  if(selectedInfo) selectedInfo.innerHTML = base + extra;

  if(skillPool){
    if(u.side==='enemy'){ skillPool.innerHTML = `<div class="partyRow small">敌方单位（AI 控制），无法操作</div>`; }
    else if(currentSide!=='player'){ skillPool.innerHTML = `<div class="partyRow small">不是你的回合</div>`; }
    else {
      skillPool.innerHTML = '';
      if(!u.dealtStart) ensureStartHand(u);
      const pool = u.skillPool || [];
      for(const sk of pool){
        const stepsOk = playerSteps>=sk.cost;
        const colorClass = sk.color || ((sk.meta && sk.meta.moveSkill) ? 'blue' : (sk.cost>=3 ? 'red' : 'green'));

        const card=document.createElement('div');
        card.className='skillCard '+colorClass;
        if(!stepsOk) card.classList.add('disabled');

        const header=document.createElement('div');
        header.style.display='flex';
        header.style.alignItems='center';
        header.style.justifyContent='space-between';

        const leftBox=document.createElement('div');
        leftBox.innerHTML = `<strong>${sk.name}</strong><div class="small">${sk.desc||''}</div>`;

        const rightBox=document.createElement('div');
        rightBox.textContent = `${sk.cost} 步`;

        const discardBtn=document.createElement('button');
        discardBtn.textContent='弃置';
        discardBtn.className='discardBtn';
        discardBtn.style.marginLeft='8px';
        discardBtn.style.fontSize='12px';
        discardBtn.style.padding='2px 6px';
        discardBtn.addEventListener('click',(e)=>{ e.stopPropagation(); if(interactionLocked) return; discardSkill(u, sk); });

        const rightWrap=document.createElement('div');
        rightWrap.style.display='flex';
        rightWrap.style.alignItems='center';
        rightWrap.style.gap='6px';
        rightWrap.appendChild(rightBox);
        rightWrap.appendChild(discardBtn);

        header.appendChild(leftBox);
        header.appendChild(rightWrap);
        card.appendChild(header);

        card.addEventListener('contextmenu',(e)=>{ e.preventDefault(); if(interactionLocked) return; discardSkill(u,sk); });
        card.addEventListener('click', ()=>{
          if(interactionLocked) return;
          if(!stepsOk){ appendLog('步数不足'); return; }
          if(u.status.stunned){ appendLog(`${u.name} 眩晕中`); return; }
          if(u.hp<=0){ appendLog(`${u.name} 已阵亡，无法行动`); return; }
          if(sk.meta && sk.meta.moveSkill && !canUnitMove(u)){ appendLog(`${u.name} 处于姿态中，无法移动`); return; }
          // Khathia restriction: cannot cast skill after moving
          if(u.id === 'khathia' && u.stepsMovedThisTurn > 0){
            appendLog(`${u.name} 已移动，本回合不能再施放技能`);
            return;
          }
          
          startSkillAiming(u, sk);
        });

        skillPool.appendChild(card);
      }
    }
  }

  clearHighlights();
  if(u.side===currentSide && !u.status.stunned && u.side==='player' && canUnitMove(u)){
    const moves=range_move_radius(u,1).filter(p=>!getUnitAt(p.r,p.c));
    for(const m of moves){ const key=`${m.r},${m.c}`; highlighted.add(key); markCell(m.r,m.c,'move'); }
  }
}
function clearHighlights(){ highlighted.clear(); document.querySelectorAll('.cell').forEach(cell=>cell.classList.remove('highlight-move','highlight-skill','highlight-skill-target','pulse','highlight-tele','highlight-imp','highlight-stage')); }
function markCell(r,c,kind){
  const cell=getCellEl(r,c);
  if(cell && !cell.classList.contains('void')){
    cell.classList.add(kind==='move'?'highlight-move':(kind==='target'?'highlight-skill-target':'highlight-skill'));
  }
}

function registerUnitMove(u){
  if(!u) return;
  u.stepsMovedThisTurn = (u.stepsMovedThisTurn || 0) + 1;
}

// —— 回合与被动（含“恢复”/Neyla 保底/姿态结算） —— 
function applyParalysisAtTurnStart(side){
  const team = Object.values(units).filter(u=>u.side===side && u.hp>0);
  let totalPar = team.reduce((s,u)=> s + (u.status.paralyzed||0), 0);
  if(totalPar>0){
    if(side==='player'){ const before=playerSteps; playerSteps = Math.max(0, playerSteps - totalPar); appendLog(`恐惧/减步：玩家 -${totalPar} 步（${before} -> ${playerSteps}）`); }
    else { const before=enemySteps; enemySteps = Math.max(0, enemySteps - totalPar); appendLog(`恐惧/减步：敌方 -${totalPar} 步（${before} -> ${enemySteps}）`); }
    for(const u of team) u.status.paralyzed = 0;
    updateStepsUI();
  }
}
function avg(arr){ if(!arr || arr.length===0) return null; return Math.floor(arr.reduce((s,u)=>s+u.level,0)/arr.length); }
function applyLevelSuppression(){
  const playerAvg = avg(Object.values(units).filter(u=>u.side==='player' && u.hp>0));
  const enemyAvg  = avg(Object.values(units).filter(u=>u.side==='enemy' && u.hp>0));
  if(playerAvg===null||enemyAvg===null) return;
  if(playerAvg>enemyAvg){ const add=Math.floor((playerAvg-enemyAvg)/5); if(add>0){ playerSteps += add; appendLog(`等级压制：玩家 +${add} 步`); } }
  else if(enemyAvg>playerAvg){ const add=Math.floor((enemyAvg-playerAvg)/5); if(add>0){ enemySteps += add; appendLog(`敌方 +${add} 步（等级压制）`); } }
  updateStepsUI();
}
function processUnitsTurnStart(side){
  for(const id in units){
    const u=units[id];
    if(u.side!==side || u.hp<=0) continue;

    u.actionsThisTurn = 0;
    u.turnsStarted = (u.turnsStarted||0) + 1;
    u.stepsMovedThisTurn = 0;
    u._designPenaltyTriggered = false;
    u._usedSkillThisTurn = false;

    if(u.id==='khathia' && side==='enemy' && u.turnsStarted % 5 === 0){
      const before = enemySteps;
      enemySteps = Math.max(0, enemySteps - 2);
      if(before !== enemySteps){ appendLog('疲劳的躯体：Khathia 本回合额外 -2 步'); updateStepsUI(); }
    }

    const extraDraw = Math.max(0, u.turnsStarted - 1);
    if(extraDraw>0) drawSkills(u, extraDraw);

    if(u._stanceType && u._stanceTurns>0){
      if(u._stanceSpPerTurn>0){
        const beforeSP = u.sp;
        u.sp = Math.min(u.maxSp, u.sp + u._stanceSpPerTurn);
        syncSpBroken(u);
        showGainFloat(u,0,u.sp-beforeSP);
        appendLog(`${u.name} 的${u._stanceType==='defense'?'防御':'反伤'}姿态：+${u._stanceSpPerTurn} SP`);
      }
      u._stanceTurns = Math.max(0, u._stanceTurns - 1);
      if(u._stanceTurns===0){
        clearStance(u);
      }
    }

    if(u.spPendingRestore!=null){
      const val = Math.min(u.maxSp, u.spPendingRestore);
      u.sp = val; syncSpBroken(u); u.spPendingRestore = null;
      appendLog(`${u.name} 的 SP 自动恢复至 ${val}`); showGainFloat(u,0,val);
    }

    if(u.status.recoverStacks && u.status.recoverStacks > 0){
      const before = u.hp;
      u.hp = Math.min(u.maxHp, u.hp + 5);
      u.status.recoverStacks = Math.max(0, u.status.recoverStacks - 1);
      showGainFloat(u,u.hp-before,0);
      appendLog(`${u.name} 的“恢复”触发：+5HP（剩余 ${u.status.recoverStacks}）`);
    }

    if(u.status.bleed && u.status.bleed>0){
      const bleedDmg = Math.max(1, Math.floor(u.maxHp*0.05));
      damageUnit(u.id, bleedDmg, 0, `${u.name} 因流血受损`, null);
      u.status.bleed = Math.max(0, u.status.bleed-1);
    }

    if(u.status.resentStacks && u.status.resentStacks>0){
      const loss = Math.max(1, Math.floor(u.maxSp * 0.05));
      const removed = applySpDamage(u, loss, {reason:`${u.name} 被怨念侵蚀：SP -{delta}`});
      if(removed>0){
        u.status.resentStacks = Math.max(0, u.status.resentStacks - 1);
      } else {
        u.status.resentStacks = Math.max(0, u.status.resentStacks - 1);
      }
    }
  }
}
function processUnitsTurnEnd(side){
  for(const id in units){
    const u=units[id];
    if(u.side!==side) continue;
    if(u.id==='adora' && u.passives.includes('calmAnalysis')){
      if((u.actionsThisTurn||0)===0){
        u.sp = Math.min(u.maxSp, u.sp + 10);
        syncSpBroken(u);
        appendLog('Adora 冷静分析：+10SP'); showGainFloat(u,0,10);
      }
    }
    if(u.id==='karma' && u.consecAttacks>0){ appendLog('Karma 连击在回合结束时重置'); u.consecAttacks=0; }
  }
  for(const id in units){
    const u=units[id];
    if(u.side!==side) continue;
    if(u.status.stunned>0){
      const next = Math.max(0, u.status.stunned-1);
      updateStatusStacks(u,'stunned', next, {label:'眩晕', type:'debuff'});
      appendLog(`${u.name} 的眩晕减少 1（剩余 ${u.status.stunned}）`);
    }
  }
}
function applyEndOfRoundPassives(){
  const adora = units['adora'];
  if(adora && adora.hp>0 && adora.passives.includes('proximityHeal')){
    for(const oid in units){
      const v=units[oid];
      if(!v || v.id===adora.id || v.side!==adora.side || v.hp<=0) continue;
      if(Math.max(Math.abs(v.r-adora.r), Math.abs(v.c-adora.c)) <= 3){
        const heal = Math.max(1, Math.floor(v.maxHp*0.05));
        v.hp = Math.min(v.maxHp, v.hp + heal);
        v.sp = Math.min(v.maxSp, v.sp + 5);
        syncSpBroken(v);
        appendLog(`Adora 邻近治疗：为 ${v.name} 恢复 ${heal} HP 和 5 SP`);
        showGainFloat(v,heal,5);
      }
    }
  }
}
function finishEnemyTurn(){
  clearAIWatchdog();
  processUnitsTurnEnd('enemy');
  roundsPassed += 1;
  applyEndOfRoundPassives();

  updateStepsUI();
  setTimeout(()=>{
    currentSide='player';
    playerSteps=computeBaseSteps();
    if(playerBonusStepsNextTurn>0){
      const bonus = playerBonusStepsNextTurn;
      playerSteps += bonus;
      appendLog(`先苦后甜：玩家额外 +${bonus} 步`);
      playerBonusStepsNextTurn = 0;
    }
    appendLog('敌方回合结束，玩家回合开始');
    applyLevelSuppression();
    applyParalysisAtTurnStart('player');
    processUnitsTurnStart('player');
    renderAll();
  }, 300);
}
function endTurn(){
  clearAllSelection();
  if(currentSide==='player'){
    appendLog('玩家结束回合');
    playerSteps = 0;
    updateStepsUI();
    checkEndOfTurn();
  } else {
    appendLog('敌方结束回合');
    // finishEnemyTurn() 会在敌方步数已被耗尽时被调用
    finishEnemyTurn();
  }
}

// —— 敌方 AI：保证用尽全部步数（无技能时必向玩家逼近） —— 
function distanceForAI(u,target){
  const baseR = u.size===2 ? (u.r+0.5) : u.r;
  const baseC = u.size===2 ? (u.c+0.5) : u.c;
  return Math.abs(baseR - target.r) + Math.abs(baseC - target.c);
}
function isWalkableForUnit(u, r, c){
  if(u.size===2) return canPlace2x2(u, r, c);
  if(!clampCell(r,c)) return false;
  const occ = getUnitAt(r,c);
  return !occ || occ===u;
}
function neighborsOf(u, r, c){
  const res=[];
  for(const dir of Object.keys(DIRS)){
    const d=DIRS[dir];
    const rr=r+d.dr, cc=c+d.dc;
    if(isWalkableForUnit(u, rr, cc)) res.push({r:rr, c:cc, dir});
  }
  return res;
}
function goalAdjCellsForTargets(u, targets){
  const goals=[];
  const seen=new Set();
  for(const t of targets){
    const adj = range_adjacent(t);
    for(const p of adj){
      const k=`${p.r},${p.c}`;
      if(seen.has(k)) continue;
      if(isWalkableForUnit(u, p.r, p.c) && !getUnitAt(p.r,p.c)){
        goals.push({r:p.r, c:p.c});
        seen.add(k);
      }
    }
  }
  return goals;
}
function bfsNextStepTowardAny(u, targets, maxExplore=4000){
  const goals = goalAdjCellsForTargets(u, targets);
  if(goals.length===0) return null;
  const goalSet = new Set(goals.map(g=>`${g.r},${g.c}`));

  const q=[];
  const prev=new Map();
  const startKey = `${u.r},${u.c}`;
  q.push({r:u.r, c:u.c});
  prev.set(startKey, null);
  let foundKey=null;

  while(q.length && prev.size < maxExplore){
    const cur=q.shift();
    const ck=`${cur.r},${cur.c}`;
    if(goalSet.has(ck)){ foundKey=ck; break; }
    const ns = neighborsOf(u, cur.r, cur.c);
    for(const n of ns){
      const nk=`${n.r},${n.c}`;
      if(!prev.has(nk)){
        prev.set(nk, ck);
        q.push({r:n.r, c:n.c});
      }
    }
  }
  if(!foundKey) return null;

  let stepKey=foundKey, back=prev.get(stepKey);
  while(back && back!==startKey){
    stepKey = back;
    back = prev.get(stepKey);
  }
  const [sr, sc] = (back===null? foundKey : stepKey).split(',').map(Number);
  const dir = cardinalDirFromDelta(sr - u.r, sc - u.c);
  return {r:sr, c:sc, dir};
}
function tryStepsToward(u, target){
  const prefs=[];
  const baseC = u.size===2 ? (u.c+0.5) : u.c;
  const baseR = u.size===2 ? (u.r+0.5) : u.r;
  const dc=Math.sign(target.c - baseC);
  const dr=Math.sign(target.r - baseR);
  if(Math.abs(target.c-baseC) >= Math.abs(target.r-baseR)){
    if(dc!==0) prefs.push(dc>0?'right':'left');
    if(dr!==0) prefs.push(dr>0?'down':'up');
  } else {
    if(dr!==0) prefs.push(dr>0?'down':'up');
    if(dc!==0) prefs.push(dc>0?'right':'left');
  }
  for(const k of ['up','down','left','right']) if(!prefs.includes(k)) prefs.push(k);

  for(const dir of prefs){
    const cand = forwardCellAt(u,dir,1);
    if(!cand) continue;
    if(u.size===2){
      if(canPlace2x2(u, cand.r, cand.c)){ u.r=cand.r; u.c=cand.c; setUnitFacing(u, dir); registerUnitMove(u); return {moved:true}; }
    } else {
      if(!getUnitAt(cand.r,cand.c)){ u.r=cand.r; u.c=cand.c; setUnitFacing(u, dir); registerUnitMove(u); return {moved:true}; }
    }
  }
  return {moved:false};
}
function computeRallyPoint(){
  const boss = units['khathia'];
  if(boss && boss.hp>0) return {r:boss.r, c:boss.c};
  const allies = Object.values(units).filter(x=>x.side==='enemy' && x.hp>0);
  if(allies.length===0) return {r:Math.ceil(ROWS/2), c:Math.ceil(COLS/2)};
  const avgR = Math.round(allies.reduce((s,a)=>s+a.r,0)/allies.length);
  const avgC = Math.round(allies.reduce((s,a)=>s+a.c,0)/allies.length);
  return {r:avgR, c:avgC};
}
function computeCellsForSkill(u, sk, dir){
  try{ return sk.rangeFn(u, dir||u.facing, null) || []; }catch(e){ return []; }
}
function aiAwait(ms){ return new Promise(res=>setTimeout(res, ms)); }

function enemyLivingEnemies(){ return Object.values(units).filter(u=>u.side==='enemy' && u.hp>0); }
function enemyLivingPlayers(){ return Object.values(units).filter(u=>u.side==='player' && u.hp>0); }

function buildSkillCandidates(en){
  const skillset = (en.skillPool && en.skillPool.length) ? en.skillPool : [];
  const candidates=[];
  for(const sk of skillset){
    if(sk.cost>enemySteps) continue;
    try{
      // 自我增益先（锁链缠绕/堡垒/反伤）
      const selfCells = sk.rangeFn(en, en.facing, null) || [];
      const isSelfOnly = selfCells.length>0 && selfCells.every(c=>c.r===en.r && c.c===en.c);
      const isBuffName = ['痛苦咆哮'].includes(sk.name);
      const canUseBuff = isBuffName && (!en._stanceType || en._stanceTurns<=0);
      if(isSelfOnly && isBuffName && canUseBuff){
        candidates.push({sk, dir:en.facing, score: 22}); // 自保最高
        continue;
      }

      const dirs = Object.keys(DIRS);
      const isAdjSkill = ['血肉之刃','怨念之爪','沙包大的拳头','短匕轻挥'].includes(sk.name);
      if(isAdjSkill){
        const adj = range_adjacent(en);
        for(const c of adj){
          const tu=getUnitAt(c.r,c.c);
          if(tu && tu.side==='player'){ candidates.push({sk, dir:c.dir, targetUnit:tu, score: 16}); }
        }
      } else if(sk.meta && sk.meta.cellTargeting){
        const cells = sk.rangeFn(en, en.facing, null) || [];
        let best=null, bestScore=-1;
        for(const c of cells){
          const tu=getUnitAt(c.r,c.c);
          if(tu && tu.side==='player' && tu.hp>0){
            const hpRatio = tu.hp/tu.maxHp;
            const sc = 18 + Math.floor((1-hpRatio)*20);
            if(sc>bestScore){ bestScore=sc; best={sk, targetUnit:tu, score:sc}; }
          }
        }
        if(best) candidates.push(best);
      } else {
        for(const d of dirs){
          const cells = sk.rangeFn(en,d,null) || [];
          let hits=0, set=new Set();
          for(const c of cells){
            const tu=getUnitAt(c.r,c.c);
            if(tu && tu.side==='player' && !set.has(tu.id)){ set.add(tu.id); hits++; }
          }
          if(hits>0) candidates.push({sk, dir:d, score: 10 + hits*8});
        }
      }
    } catch(e){
      console.error('AI 技能评估错误', e);
      appendLog(`[AI错误] ${en.name} 评估 ${sk.name} 失败：${e.message}`);
    }
  }
  candidates.sort((a,b)=> b.score-a.score);
  return candidates;
}
async function execEnemySkillCandidate(en, cand){
  enemySteps = Math.max(0, enemySteps - cand.sk.cost);
  updateStepsUI();

  const cells = cand.targetUnit
    ? [{r:cand.targetUnit.r, c:cand.targetUnit.c}]
    : computeCellsForSkill(en, cand.dir, cand.dir);

  clearHighlights();
  cells.forEach(c=> markCell(c.r,c.c,'skill'));
  await aiAwait(ENEMY_WINDUP_MS);
  clearHighlights();

  let faceDir = null;
  if(cand.targetUnit){
    const tu = cand.targetUnit;
    if(tu.r !== en.r || tu.c !== en.c){
      faceDir = cardinalDirFromDelta(tu.r - en.r, tu.c - en.c);
    }
  } else if(cand.dir){
    faceDir = cand.dir;
  }
  if(faceDir){
    setUnitFacing(en, faceDir);
  }

  try{
    if(cand.targetUnit && cand.sk.meta && cand.sk.meta.cellTargeting){
      await cand.sk.execFn(en, {r:cand.targetUnit.r, c:cand.targetUnit.c});
    } else if(cand.targetUnit){
      await cand.sk.execFn(en, cand.targetUnit);
    } else if(cand.sk.estimate && cand.sk.estimate.aoe){
      await cand.sk.execFn(en, {dir:cand.dir});
    } else {
      await cand.sk.execFn(en, {dir:cand.dir});
    }
    consumeCardFromHand(en, cand.sk);
    renderAll();
    return true;
  } catch(e){
    console.error('AI 技能施放错误', e);
    appendLog(`[AI错误] ${en.name} 施放 ${cand.sk.name} 失败：${e.message}`);
    return false;
  }
}
function stepTowardNearestPlayer(en){
  if(!canUnitMove(en)) return false;
  const players = enemyLivingPlayers();
  if(players.length===0) return false;
  // BFS toward any player's adjacent cell
  const step = bfsNextStepTowardAny(en, players);
  if(step){
    setUnitFacing(en, step.dir || en.facing);
    en.r = step.r; en.c = step.c;
    registerUnitMove(en);
    enemySteps = Math.max(0, enemySteps - 1);
    updateStepsUI();
    cameraFocusOnCell(en.r,en.c);
    renderAll();
    appendLog(`${en.name} 逼近：向玩家方向移动 1 步`);
    return true;
  }
  // Fallback heuristic toward nearest player's position
  let nearest=players[0], md=distanceForAI(en, players[0]);
  for(const p of players){ const d=distanceForAI(en,p); if(d<md){ md=d; nearest=p; } }
  const mv = tryStepsToward(en, nearest);
  if(mv.moved){
    enemySteps = Math.max(0, enemySteps - 1);
    updateStepsUI();
    cameraFocusOnCell(en.r,en.c);
    renderAll();
    appendLog(`${en.name} 逼近：向最近玩家挪动 1 步`);
    return true;
  }
  return false;
}
function wasteOneEnemyStep(reason='敌方犹豫不决，浪费了 1 步'){
  if(enemySteps>0){
    enemySteps = Math.max(0, enemySteps - 1);
    appendLog(reason);
    updateStepsUI();
    return true;
  }
  return false;
}

async function exhaustEnemySteps(){
  aiLoopToken++; const token = aiLoopToken;
  armAIWatchdog(token, 20000);

  // 主循环：直到步数归零或一方全灭
  while(currentSide==='enemy' && enemySteps>0){
    if(token !== aiLoopToken) break;

    // 快速终止条件
    const livingEnemies = enemyLivingEnemies();
    const players = enemyLivingPlayers();
    if(livingEnemies.length===0 || players.length===0){
      enemySteps = 0;
      updateStepsUI();
      break;
    }

    let progressedThisRound = false;

    // 轮询每个单位各尝试一次“动作”
    for(const en of livingEnemies){
      if(enemySteps<=0) break;
      if(!en || en.hp<=0) continue;
      if(en.status.stunned){ aiLog(en,'眩晕跳过'); continue; }
      if(!en.dealtStart) ensureStartHand(en);
      // 1) 尝试技能
      let didAct = false;
      const candidates = buildSkillCandidates(en);
      if(candidates.length===0 && en.id==='khathia' && !en._designPenaltyTriggered && typeof en.maxMovePerTurn==='number' && (en.stepsMovedThisTurn||0) >= en.maxMovePerTurn){
        applyKhathiaDesignPenalty();
        en._designPenaltyTriggered = true;
        if(enemySteps>0){ enemySteps = Math.max(0, enemySteps - 1); updateStepsUI(); }
        progressedThisRound = true;
        await aiAwait(140);
        continue;
      }
      if(candidates.length>0){
        didAct = await execEnemySkillCandidate(en, candidates[0]);
        if(didAct){
          progressedThisRound = true;
          await aiAwait(600); // 技能施放后延迟，避免连续技能过快
        }
      }

      // 2) 无技能可用 → 向玩家移动
      if(!didAct && enemySteps>0){
        const moved = stepTowardNearestPlayer(en);
        if(moved){
          progressedThisRound = true;
          await aiAwait(140);
        }
      }

      // 3) 仍无动作 → 尝试原地随机挪步（只为消步）
      if(!didAct && enemySteps>0 && !progressedThisRound){
        const neigh = neighborsOf(en, en.r, en.c).filter(p=> !getUnitAt(p.r,p.c));
        if(canUnitMove(en) && neigh.length){
          const pick = neigh[Math.floor(Math.random()*neigh.length)];
          en.r = pick.r; en.c = pick.c;
          setUnitFacing(en, pick.dir || en.facing);
          registerUnitMove(en);
          enemySteps = Math.max(0, enemySteps - 1);
          updateStepsUI();
          cameraFocusOnCell(en.r,en.c);
          renderAll();
          appendLog(`${en.name} 试探性移动：消耗 1 步`);
          progressedThisRound = true;
          await aiAwait(120);
        }
      }
    }

    // 整轮无人动作 → 强行消步直到 0（防止卡住）
    if(!progressedThisRound){
      // 尝试对一个可移动单位强制朝集合点靠拢
      const anyMovable = enemyLivingEnemies().find(e=> canUnitMove(e) && neighborsOf(e, e.r, e.c).some(p=>!getUnitAt(p.r,p.c)));
      if(anyMovable){
        const rally = computeRallyPoint();
        const mv = tryStepsToward(anyMovable, rally);
        if(mv.moved){
          enemySteps = Math.max(0, enemySteps - 1);
          updateStepsUI();
          cameraFocusOnCell(anyMovable.r,anyMovable.c);
          renderAll();
          appendLog(`${anyMovable.name} 整队：向集合点挪动 1 步`);
          await aiAwait(120);
          continue; // 继续下一轮
        }
      }
      // 仍无法动作 → 直接丢弃步数
      if(enemySteps>0){
        wasteOneEnemyStep();
        await aiAwait(80);
      }
    }
  }

  clearAIWatchdog();
}

async function enemyTurn(){
  renderAll();
  const livingEnemies = enemyLivingEnemies();
  const livingPlayers = enemyLivingPlayers();
  if(livingEnemies.length===0 || livingPlayers.length===0){
    enemySteps = 0; updateStepsUI();
    return finishEnemyTurn();
  }
  appendLog('敌方开始行动');

  enemyActionCameraLock = true;

  // 用尽步数
  await exhaustEnemySteps();

  // 兜底：确保步数为 0
  if(enemySteps>0){
    appendLog('兜底：将剩余敌方步数清零');
    enemySteps = 0; updateStepsUI();
  }

  enemyActionCameraLock = false;
  cameraReset();

  // 正式结束敌方回合
  finishEnemyTurn();
}

// —— 胜负/渲染循环 ——
function checkWin(){
  const enemiesAlive = Object.values(units).some(u=>u.side==='enemy' && u.hp>0);
  const playersAlive = Object.values(units).some(u=>u.side==='player' && u.hp>0);
  if(!enemiesAlive){ showAccomplish(); return true; }
  if(!playersAlive){ appendLog('全灭，失败（本 demo 未实现失败界面）'); return true; }
  return false;
}
function showAccomplish(){
  if(!accomplish) return;
  accomplish.classList.remove('hidden');
  if(damageSummary){
    damageSummary.innerHTML='';
    const wrap=document.createElement('div'); wrap.className='acctable';
    for(const id of ['adora','dario','karma']){
      const u=units[id];
      const row=document.createElement('div'); row.className='row';
      row.innerHTML=`<strong>${u.name}</strong><div class="small">造成伤害: ${u.dmgDone}，受到: ${u.maxHp - u.hp}</div>`;
      wrap.appendChild(row);
    }
    damageSummary.appendChild(wrap);
  }
  const btn=document.getElementById('confirmBtn');
  if(btn) btn.onclick=()=>{ accomplish.classList.add('hidden'); appendLog('通关!'); };
}
function renderAll(){
  buildGrid();
  placeUnits();
  renderStatus();
  updateStepsUI();
  if(checkWin()) return;
}
function checkEndOfTurn(){
  if(currentSide==='player' && playerSteps<=0){
    appendLog('玩家步数耗尽，轮到敌方');
    processUnitsTurnEnd('player');
    currentSide='enemy';
    enemySteps=computeBaseSteps();
    applyLevelSuppression();
    applyParalysisAtTurnStart('enemy');
    processUnitsTurnStart('enemy');
    // 敌方回合：保证用尽步数
    setTimeout(()=>{ enemyTurn(); }, 200);
    return;
  }
  if(currentSide==='enemy' && enemySteps<=0){
    appendLog('敌方步数耗尽，轮到玩家');
    finishEnemyTurn();
    return;
  }
}

// —— Haz 力挽狂澜触发检测（含卡池替换规则） —— 

// —— 初始化 —— 
document.addEventListener('DOMContentLoaded', ()=>{
  battleAreaEl = document.getElementById('battleArea');
  mapPaneEl = document.getElementById('mapPane');
  cameraEl = battleAreaEl;
  playerStepsEl = document.getElementById('playerSteps');
  enemyStepsEl = document.getElementById('enemySteps');
  roundCountEl = document.getElementById('roundCount');
  partyStatus = document.getElementById('partyStatus');
  selectedInfo = document.getElementById('selectedInfo');
  skillPool = document.getElementById('skillPool');
  logEl = document.getElementById('log');
  accomplish = document.getElementById('accomplish');
  damageSummary = document.getElementById('damageSummary');

  updateCameraBounds();
  createCameraControls();
  registerCameraInputs();
  cameraReset({immediate:true});
  startCameraLoop();

  // 掩体（不可进入）
  injectFXStyles();

  // 起手手牌
  for(const id in units){ const u=units[id]; if(u.hp>0) ensureStartHand(u); }

  playerSteps = computeBaseSteps();
  enemySteps = computeBaseSteps();

  renderAll();
  updateCameraBounds();
  applyCameraTransform();

  // 初次渲染后延迟刷新 2x2 覆盖
  setTimeout(()=> refreshLargeOverlays(), 0);
  setTimeout(()=> refreshLargeOverlays(), 240);
  if('requestAnimationFrame' in window){
    requestAnimationFrame(()=> refreshLargeOverlays());
  }
  window.addEventListener('load', ()=> refreshLargeOverlays());

  appendLog('疲惫的极限：地图 10x20，全场无额外掩体。');
  appendLog('Khathia 需叠满4层眩晕才会进入眩晕状态，SP 崩溃将触发特殊疲劳崩溃。');
  appendLog('怨念会在回合开始时吞噬目标的 5% SP，记得及时清除。');

  const endTurnBtn=document.getElementById('endTurnBtn');
  if(endTurnBtn) endTurnBtn.addEventListener('click', ()=>{ if(interactionLocked) return; endTurn(); });

  // GOD'S WILL 按钮
  godsWillBtn = document.createElement('button');
  godsWillBtn.id = 'godsWillBtn';
  godsWillBtn.textContent = "GOD'S WILL";
  godsWillBtn.title = '调试：点击后选择任意单位 → 杀死或留 1 HP（ESC 取消）';
  godsWillBtn.onclick = (e)=>{
    e.stopPropagation();
    if(interactionLocked || godsWillLockedOut) return;
    if(!godsWillUnlocked){
      const answer = prompt('请输入 GOD\'S WILL 密码');
      const normalized = (answer ?? '').trim();
      if(normalized === GODS_WILL_PASSWORD){
        godsWillUnlocked = true;
        if(godsWillBtn){
          godsWillBtn.disabled = false;
          godsWillBtn.classList.remove('locked');
          godsWillBtn.title = 'GOD’S WILL：点击后选择任意单位 → 杀死或留 1 HP（ESC 取消）';
        }
        appendLog('GOD’S WILL：密码验证通过，功能解锁');
      } else {
        godsWillLockedOut = true;
        if(godsWillBtn){
          godsWillBtn.disabled = true;
          godsWillBtn.classList.add('locked');
          godsWillBtn.title = 'GOD’S WILL：密码错误，功能已锁定';
        }
        appendLog('GOD’S WILL：密码错误，按钮失效');
        return;
      }
    }
    toggleGodsWill();
  };
  document.body.appendChild(godsWillBtn);

  // Full Screen 按钮
  fsBtn = document.createElement('button');
  fsBtn.id = 'fullscreenBtn';
  fsBtn.textContent = 'Full Screen';
  fsBtn.title = '切换全屏模式';
  fsBtn.onclick = (e)=>{ e.stopPropagation(); if(interactionLocked) return; toggleFullscreen(); };
  document.body.appendChild(fsBtn);

  // ESC 取消 GOD’S WILL
  window.addEventListener('keydown',(e)=>{
    if(e.key === 'Escape' && godsWillArmed){
      disarmGodsWill();
    }
  });

  // 视口改变时刷新 2x2 覆盖和菜单
  let _resizeTimer=null;
  window.addEventListener('resize', ()=>{
    if(_resizeTimer) clearTimeout(_resizeTimer);
    _resizeTimer = setTimeout(()=>{
      refreshLargeOverlays();
      if(godsWillMenuEl && godsWillMenuEl.isConnected){
        godsWillMenuEl.remove();
        godsWillMenuEl=null;
        if(godsWillArmed) appendLog('GOD’S WILL 菜单因窗口变化已移除，请重新点击单位');
      }
      updateCameraBounds();
    }, 120);
  });

  applyLevelSuppression();
  applyParalysisAtTurnStart('player');
  processUnitsTurnStart('player');
  updateStepsUI();
  setTimeout(()=> playIntroCinematic(), 80);
});
