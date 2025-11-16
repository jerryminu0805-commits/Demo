// 2D 回合制 RPG Demo - 七海作战队Boss战
// 变更摘要：
// - 注入基础栅格/单位样式与 --cell 默认值，修复“又没角色了”（无 CSS 时看不到格子/单位）。
// - AI：加入 BFS 寻路与兜底移动，避免整轮只动队长或卡住不用完步数。
// - 多阶段技能：每一阶段即时演出与结算（青→红→结算→黄阶段标记）。
// - Adora：略懂的医术！；电击装置会叠1层眩晕叠层与恐惧减步。
// - Karma：深呼吸 被动+10% 只要卡在池里未被使用，主动用为回蓝+10HP。
// - UI：新增 Full Screen（全屏）按钮，支持原生全屏与模拟全屏双方案；修复 2x2 单位（Tusk）初始可能不在视区的覆盖刷新。
// - GOD’S WILL：增强健壮性（按钮/菜单/点击单位三路触发），并在全屏/窗口变化后稳定可用。
// - Neyla：压迫后“终末之影”规则：每回合保证手牌至多一张；如无且卡满则随机替换一张为“终末之影”。
// - 调整：双钩牵制 → Neyla 常态技能（2步，红，前3格内优先最近，单体）；终焉礼炮不再标注为压迫技能（常态/压迫均可用）。
// - 调整：Katz「反复鞭尸」→ 3步 前3格AOE，10/15伤害+每段+5SP，按自身SP百分比重复（最多5次），出现率50%，压迫后不再出现。
// - 调整：Neyla 常态也可抽到「终末之影」（30%）。
// - 调整：Kyn「影杀之舞」→ 常态2步 3x3 AOE 30伤害（不受掩体）并立即免费位移1格（50%），压迫后不再出现；压迫后新增「自我了断。。」。
// - 状态栏：被“猎杀标记”的单位在 Debuff 栏显示“猎杀标记”。
// - 修复：Tusk（2x2）被点击锁定时，技能指向将智能映射到其四个覆盖格之一，避免“进入姿态后无法被选中/命中”（具体逻辑在 part2 的 overlay 点击处理）。
// - 新增保证：在“敌方回合结束，玩家回合开始”之前，敌方必定把步数用到 0（若无技能则自动向玩家单位逼近），详见 part2 的 exhaustEnemySteps 与 finishEnemyTurn 逻辑。

let ROWS = 9;
let COLS = 26;

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
let _distanceDisplay = null;
let fxLayer = null;
let cameraEl = null;
let battleAreaEl = null;
let mapPaneEl = null;
let cameraControlsEl = null;
let roundBannerEl = null;
let introDialogEl = null;
let bossBGM = null;

let playerStepsEl, enemyStepsEl, roundCountEl, partyStatus, selectedInfo, skillPool, accomplish, damageSummary;

let hazMarkedTargetId = null;
let hazTeamCollapsed = false;

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
  // 9x26 map - no void cells for this battle
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
    sp: maxSp, maxSp,
    restoreOnZeroPct, spZeroHpPenalty,
    facing: side==='player' ? 'right' : 'left',
    status: {
      stunned: 0,
      paralyzed: 0,
      bleed: 0,
      hazBleedTurns: 0,
      recoverStacks: 0,          // “恢复”Buff 层数（每大回合开始消耗一层，+5HP）
      jixueStacks: 0,            // “鸡血”Buff 层数（下一次攻击伤害x2）
      dependStacks: 0,           // “依赖”Buff 层数（下一次攻击真实伤害，结算后清空自身SP）
      agileStacks: 0,            // "灵活"Buff 层数（让敌方30%几率miss，miss消耗一层）
      affirmationStacks: 0,      // "肯定"Buff 层数（免疫一次SP伤害，多阶段攻击全阶段免疫，消耗一层）
    },
    dmgDone: 0,
    skillPool: [],
    passives: passives.slice(),
    actionsThisTurn: 0,
    consecAttacks: 0,
    turnsStarted: 0,
    dealtStart: false,
    team: extra.team || null,
    oppression: false,
    chainShieldTurns: 0,
    chainShieldRetaliate: 0,
    tuskRageStacks: 0,
    stunThreshold: extra.stunThreshold || 1,
    _staggerStacks: 0,
    pullImmune: !!extra.pullImmune,
    _spBroken: false,
    _spCrashVuln: false,
    spPendingRestore: null,
    _comeback: false,
    tutorialTurnCount: 0,      // 用于跟踪"自我激励教程"的回合数

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
// 玩家 - 旧情未了关卡
units['karma'] = createUnit('karma','Karma','player',50, 5, 22, 200,50, 0.5,20, ['violentAddiction','toughBody','pride']);
// Boss - Lirathe
units['lirathe'] = createUnit('lirathe','Lirathe/利拉斯-赫雷西第五干部','enemy',50, 5, 5, 700,80, 0.75,20, ['dancerDream','achingHeart','swiftAgility','rebirth','reluctance'], {stunThreshold:4, pullImmune:true});

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
  .skill-fx.bloom-vine { width: 150px; height: 190px; opacity: 0; filter: drop-shadow(0 12px 26px rgba(255, 82, 120, 0.45));
                         animation: bloom-vine-fade 820ms ease-out forwards; }
  .skill-fx.bloom-vine .vine { position:absolute; left:50%; bottom:22%; width:18px; height:110px; border-radius:999px;
                               background: linear-gradient(180deg, rgba(122,0,18,0.95), rgba(255,102,138,0.78));
                               transform: translate(-50%, 30%) scaleY(0.25); opacity:0; animation: bloom-vine-grow 520ms ease-out forwards; }
  .skill-fx.bloom-vine .tendrils { position:absolute; left:50%; bottom:28%; width:120px; height:90px; pointer-events:none; transform: translateX(-50%); }
  .skill-fx.bloom-vine .tendril { position:absolute; bottom:38%; width:62px; height:12px; border-radius:999px;
                                  background: radial-gradient(circle, rgba(255,150,176,0.9) 0%, rgba(255,150,176,0));
                                  opacity:0; animation: bloom-vine-tendril 620ms ease-out forwards; }
  .skill-fx.bloom-vine .tendril.one { left:4px; transform-origin:left 50%; transform: rotate(-34deg); }
  .skill-fx.bloom-vine .tendril.two { right:4px; transform-origin:right 50%; transform: rotate(32deg); animation-delay: 140ms; }
  .skill-fx.bloom-vine .flower { position:absolute; left:50%; bottom: calc(22% + 112px); width:74px; height:74px; border-radius:50%;
                                 background: radial-gradient(circle, rgba(255,214,224,0.95) 0%, rgba(255,98,132,0.82) 46%, rgba(255,0,70,0) 72%);
                                 transform: translate(-50%, 26%) scale(0.35); opacity:0; animation: bloom-vine-flower 560ms ease-out forwards; }
  .skill-fx.bloom-heal { width: 150px; height: 150px; opacity:0; filter: drop-shadow(0 8px 18px rgba(255, 120, 150, 0.45));
                         animation: bloom-heal-fade 780ms ease-out forwards; }
  .skill-fx.bloom-heal .glow { position:absolute; left:50%; top:50%; width:92%; height:92%; border-radius:50%;
                               background: radial-gradient(circle, rgba(255,120,150,0.45) 0%, rgba(255,255,255,0) 75%);
                               transform: translate(-50%, -50%) scale(0.45); opacity:0; animation: bloom-heal-glow 780ms ease-out forwards; }
  .skill-fx.bloom-heal .petals { position:absolute; inset:0; }
  .skill-fx.bloom-heal .petal { position:absolute; left:50%; top:50%; width:28px; height:54px; border-radius:16px 16px 30px 30px;
                                background: linear-gradient(180deg, rgba(255,210,220,0.92) 0%, rgba(255,94,128,0.85) 85%);
                                transform-origin:50% 90%; opacity:0; --petal-angle:0deg; --petal-delay:0ms;
                                animation: bloom-heal-petal 720ms ease-out forwards; animation-delay: var(--petal-delay); }
  .skill-fx.bloom-heal .petal[data-index="0"] { --petal-angle:-90deg; }
  .skill-fx.bloom-heal .petal[data-index="1"] { --petal-angle:-18deg; --petal-delay:60ms; }
  .skill-fx.bloom-heal .petal[data-index="2"] { --petal-angle:54deg; --petal-delay:90ms; }
  .skill-fx.bloom-heal .petal[data-index="3"] { --petal-angle:126deg; --petal-delay:120ms; }
  .skill-fx.bloom-heal .petal[data-index="4"] { --petal-angle:198deg; --petal-delay:150ms; }
  .skill-fx.bloom-heal .sparks { position:absolute; inset:0; }
  .skill-fx.bloom-heal .spark { position:absolute; left:50%; top:50%; width:12px; height:12px; border-radius:50%;
                                background: radial-gradient(circle, rgba(255,214,220,0.95) 0%, rgba(255,214,220,0) 72%);
                                opacity:0; --spark-angle:0deg; --spark-delay:0ms;
                                animation: bloom-heal-spark 680ms ease-out forwards; animation-delay: var(--spark-delay); }
  .skill-fx.bloom-heal .spark[data-index="0"] { --spark-angle:-22deg; }
  .skill-fx.bloom-heal .spark[data-index="1"] { --spark-angle:32deg; --spark-delay:40ms; }
  .skill-fx.bloom-heal .spark[data-index="2"] { --spark-angle:86deg; --spark-delay:80ms; }
  .skill-fx.bloom-heal .spark[data-index="3"] { --spark-angle:150deg; --spark-delay:100ms; }
  .skill-fx.bloom-heal .spark[data-index="4"] { --spark-angle:210deg; --spark-delay:120ms; }
  .skill-fx.bloom-heal .spark[data-index="5"] { --spark-angle:268deg; --spark-delay:150ms; }
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
  @keyframes bloom-vine-fade { 0% { opacity: 0; } 28% { opacity: 1; } 100% { opacity: 0; } }
  @keyframes bloom-vine-grow { 0% { opacity: 0; transform: translate(-50%, 36%) scaleY(0.15); }
                               55% { opacity: 1; transform: translate(-50%, 4%) scaleY(1.05); }
                               100% { opacity: 0; transform: translate(-50%, 0%) scaleY(0.85); } }
  @keyframes bloom-vine-tendril { 0% { opacity: 0; transform: scaleX(0.4) translateY(12px); }
                                  40% { opacity: 0.95; transform: scaleX(1) translateY(-6px); }
                                  100% { opacity: 0; transform: scaleX(1.1) translateY(-12px); } }
  @keyframes bloom-vine-flower { 0% { opacity: 0; transform: translate(-50%, 30%) scale(0.3); }
                                 45% { opacity: 1; transform: translate(-50%, -6%) scale(1.05); }
                                 100% { opacity: 0; transform: translate(-50%, -16%) scale(0.9); } }
  @keyframes bloom-heal-fade { 0% { opacity: 0; } 32% { opacity: 1; } 100% { opacity: 0; } }
  @keyframes bloom-heal-glow { 0% { opacity: 0; transform: translate(-50%, -50%) scale(0.45); }
                               45% { opacity: 0.85; transform: translate(-50%, -50%) scale(1.02); }
                               100% { opacity: 0; transform: translate(-50%, -50%) scale(1.32); } }
  @keyframes bloom-heal-petal { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(var(--petal-angle)) scale(0.35); }
                                40% { opacity: 1; transform: translate(-50%, -64%) rotate(var(--petal-angle)) scale(1); }
                                100% { opacity: 0; transform: translate(-50%, -72%) rotate(var(--petal-angle)) scale(0.85); } }
  @keyframes bloom-heal-spark { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(var(--spark-angle)) translateY(0) scale(0.45); }
                                35% { opacity: 1; }
                                100% { opacity: 0; transform: translate(-50%, -50%) rotate(var(--spark-angle)) translateY(-46px) scale(0.85); } }
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
function buildBloomVineSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('bloom-vine');
  node.innerHTML = `
    <div class="vine"></div>
    <div class="tendrils">
      <span class="tendril one"></span>
      <span class="tendril two"></span>
    </div>
    <div class="flower"></div>
  `;
  onAnimEndRemove(node, config.duration || 820);
  return attachSkillFx(node, anchor);
}
function buildBloomHealSkillFx({anchor, angle, config}){
  const node = makeSkillFxNode('bloom-heal');
  const petals = [];
  for(let i=0;i<5;i++){ petals.push(`<span class="petal" data-index="${i}"></span>`); }
  const sparks = [];
  for(let i=0;i<6;i++){ sparks.push(`<span class="spark" data-index="${i}"></span>`); }
  node.innerHTML = `
    <div class="glow"></div>
    <div class="petals">${petals.join('')}</div>
    <div class="sparks">${sparks.join('')}</div>
  `;
  onAnimEndRemove(node, config.duration || 780);
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
  'bloom-vine': buildBloomVineSkillFx,
  'bloom-heal': buildBloomHealSkillFx,
};
const SKILL_FX_CONFIG = {
  'adora:短匕轻挥':        {type:'slash', primary:'#ff82b6', secondary:'rgba(255,158,206,0.55)', spark:'#ffe5f5', slashes:2},
  'adora:呀！你不要靠近我呀！！': {type:'spiral', primary:'#ff9f6a', secondary:'#ffe0c1'},
  'adora:自制粉色迷你电击装置': {type:'lightning', primary:'#ff87ff', secondary:'#ffd7ff', bolts:4},
  'adora:略懂的医术！':     {type:'aura', primary:'#75e6a7', secondary:'#c6ffde', outline:'rgba(255,255,255,0.85)', glyph:'✚'},
  'adora:加油哇！':         {type:'aura', primary:'#ffcf74', secondary:'#ffe9bb', glyph:'★'},
  'adora:只能靠你了。。':   {type:'impact', primary:'#ff6161', secondary:'#ffd6d6'},
  'adora:绽放（红色）·爆裂': {type:'bloom-vine'},
  'adora:绽放（红色）·治疗': {type:'bloom-heal'},
  'adora:课本知识：刺杀一': {type:'cascade', primary:'#8B0000', secondary:'#DC143C', droplets:8},
  'adora:枪击':             {type:'beam', primary:'#ffd780', secondary:'#fff1c2', glow:'rgba(255,255,255,0.9)', variant:'adora'},
  'dario:机械爪击':         {type:'claw', primary:'#f6c55b', secondary:'#fff3c7', scratches:4, spacing:14, delayStep:22, shards:3, shardSpread:12, shardArc:10, shardStartAngle:-24, variant:'mecha', attack:{type:'swing', swings:2, spread:12, delayStep:32, variant:'mecha'}},
  'dario:枪击':             {type:'beam', primary:'#9ee0ff', secondary:'#dcf6ff', glow:'rgba(255,255,255,0.85)', variant:'dario'},
  'dario:迅捷步伐':         {type:'spiral', primary:'#7fe8ff', secondary:'#d6f8ff'},
  'dario:拿来吧你！':       {type:'claw', primary:'#ffa56a', secondary:'#ffd7b9', scratches:5},
  'dario:先苦后甜':         {type:'aura', primary:'#c9a4ff', secondary:'#eedcff', glyph:'↻'},
  'dario:撕裂伤口':         {type:'claw', primary:'#ff6b6b', secondary:'#ffb3b3', scratches:5, spacing:16},
  'dario:状态恢复':         {type:'aura', primary:'#75e6a7', secondary:'#c6ffde', glyph:'✄'},
  'karma:沙包大的拳头':     {type:'slash', primary:'#ff9059', secondary:'rgba(255,192,160,0.7)', spark:'#fff0e4', slashes:1},
  'karma:枪击':             {type:'beam', primary:'#f38fff', secondary:'#ffd9ff', glow:'rgba(255,255,255,0.85)', variant:'karma'},
  'karma:都听你的':         {type:'spiral', primary:'#ffdd77', secondary:'#fff1bd'},
  'karma:嗜血之握':         {type:'claw', primary:'#d95ffb', secondary:'#f0b8ff', scratches:3},
  'karma:深呼吸':           {type:'aura', primary:'#7ecfff', secondary:'#d7f1ff', glyph:'息'},
  'karma:肾上腺素':         {type:'aura', primary:'#ff8c69', secondary:'#ffd4c4', glyph:'💪'},
  'haz:鱼叉穿刺':           {type:'beam', primary:'#5fd9ff', secondary:'#c5f2ff', glow:'rgba(255,255,255,0.8)', variant:'harpoon'},
  'haz:深海猎杀':           {type:'slash', primary:'#4ecdf2', secondary:'rgba(170,236,255,0.6)', spark:'#e3fbff', slashes:3, attack:{type:'swing', swings:3, spread:24, delayStep:36, variant:'wide', faceTarget:false}},
  'haz:猎神之叉':           {type:'slash', primary:'#ffe373', secondary:'rgba(255,233,152,0.7)', spark:'#fff6c4', slashes:2, attack:{type:'swing', swings:2, spread:22, delayStep:30, variant:'wide', faceTarget:false}},
  'haz:锁链缠绕':           {type:'rune', primary:'#8ed8ff', secondary:'#dff3ff', variant:'chain'},
  'haz:鲸落':               {type:'cascade', primary:'#8ae8ff', secondary:'#d5f9ff', droplets:6},
  'haz:怨念滋生':           {type:'rune', primary:'#b56fff', secondary:'#eed4ff', variant:'curse'},
  'haz:付出代价':           {type:'slash', primary:'#ff6d6d', secondary:'rgba(255,158,158,0.7)', spark:'#ffd3d3', slashes:4, attack:{type:'swing', swings:3, spread:26, delayStep:30, variant:'wide', faceTarget:false}},
  'haz:仇恨之叉':           {type:'slash', primary:'#ffa365', secondary:'rgba(255,202,153,0.7)', spark:'#ffe7d4', slashes:4, attack:{type:'swing', swings:3, spread:24, delayStep:30, variant:'wide', faceTarget:false}},
  'haz:怨念滋生·恐惧':      {type:'rune', primary:'#9c60ff', secondary:'#e4ceff', variant:'fear'},
  'haz:锁链缠绕·增益':      {type:'aura', primary:'#74b2ff', secondary:'#cce0ff', glyph:'链'},
  'haz:锁链缠绕·反击':      {type:'burst', primary:'#9ad9ff', secondary:'#e3f4ff'},
  'katz:矛刺':              {type:'beam', primary:'#ff886d', secondary:'#ffd5c6', variant:'spear'},
  'katz:链式鞭击':          {type:'slash', primary:'#ff586f', secondary:'rgba(255,163,177,0.7)', spark:'#ffd2da', slashes:3},
  'katz:反复鞭尸':          {type:'slash', primary:'#ff4d9d', secondary:'rgba(255,164,210,0.7)', spark:'#ffd4ec', slashes:5},
  'katz:终焉礼炮':          {type:'beam', primary:'#ff6f3f', secondary:'#ffc8aa', variant:'cannon', length:180},
  'katz:必须抹杀一切。。':  {type:'rune', primary:'#ff6666', secondary:'#ffd1d1', variant:'obliterate'},
  'tusk:骨盾猛击':          {type:'impact', primary:'#d2c4ff', secondary:'#f1ebff'},
  'tusk:来自深海的咆哮':    {type:'burst', primary:'#84dfff', secondary:'#d3f4ff'},
  'tusk:战争堡垒':          {type:'aura', primary:'#a0b7ff', secondary:'#dde5ff', glyph:'堡'},
  'tusk:牛鲨冲撞':          {type:'impact', primary:'#ffe483', secondary:'#fff3bd'},
  'tusk:拼尽全力保卫队长':  {type:'aura', primary:'#ff9e7f', secondary:'#ffd0c2', glyph:'盾'},
  'neyla:迅捷射击':         {type:'beam', primary:'#ff7dce', secondary:'#ffd6f0', variant:'rapid'},
  'neyla:穿刺狙击':         {type:'beam', primary:'#ffdf7c', secondary:'#fff0c1', variant:'sniper', length:200},
  'neyla:双钩牵制':         {type:'claw', primary:'#ff9a9a', secondary:'#ffd8d8', scratches:2},
  'neyla:终末之影':         {type:'rune', primary:'#ff9df2', secondary:'#ffd9fa', variant:'doom'},
  'neyla:执行……':          {type:'beam', primary:'#b3a4ff', secondary:'#e8e2ff', variant:'execution', length:140},
  'kyn:迅影突刺':           {type:'slash', primary:'#8ef9ff', secondary:'rgba(206,253,255,0.7)', spark:'#f0feff', slashes:2},
  'kyn:死亡宣告':           {type:'rune', primary:'#ff8383', secondary:'#ffd6d6', variant:'doom'},
  'kyn:割喉飞刃':           {type:'slash', primary:'#ff5f9f', secondary:'rgba(255,176,212,0.7)', spark:'#ffdff0', slashes:3},
  'kyn:影杀之舞':           {type:'burst', primary:'#b57dff', secondary:'#e8d6ff', variant:'dance'},
  'kyn:自我了断。。':       {type:'impact', primary:'#7d95ff', secondary:'#d5deff'},
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
    speaker.textContent = 'Haz';
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
function stopBossBGM(){
  if(bossBGM){
    bossBGM.pause();
    bossBGM.currentTime = 0;
  }
}
async function playIntroCinematic(){
  if(introPlayed) return;
  introPlayed = true;
  setInteractionLocked(true);
  cameraReset({immediate:true});
  await sleep(260);
  const haz = units['haz'];
  if(haz && haz.hp>0){
    const zoom = clampValue(cameraState.baseScale * 1.3, cameraState.minScale, cameraState.maxScale);
    cameraFocusOnCell(haz.r, haz.c, {scale: zoom, hold:0});
    await sleep(420);
  }
  await showIntroLine('这种躲躲藏藏遮遮掩掩的人绝对不是什么好东西');
  await showIntroLine('准备好队员们，今晚不出意外的话，又能钓到一条大的。。。');
  hideIntroDialog();
  cameraReset();
  await sleep(520);
  showRoundBanner('回合一', 1800);
  // Start Boss BGM after Round 1 banner appears
  if(bossBGM){
    bossBGM.volume = 0.6;
    if(bossBGM.readyState >= 2){
      bossBGM.play().catch(e => console.log('Boss BGM autoplay blocked:', e));
    } else {
      bossBGM.addEventListener('canplay', () => {
        bossBGM.play().catch(e => console.log('Boss BGM autoplay blocked:', e));
      }, {once: true});
    }
  }
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
  const spCrashThreshold = u.spCrashThreshold !== undefined ? u.spCrashThreshold : 0;
  if(u.sp <= spCrashThreshold && !u._spBroken){
    u._spBroken = true;
    if(!u._spCrashVuln){
      u._spCrashVuln = true;
      showStatusFloat(u,'SP崩溃易伤',{type:'debuff', offsetY:-88});
      appendLog(`${u.name} 处于 SP 崩溃易伤：受到的伤害x1.5，直到眩晕解除且 SP 恢复`);
    }
    
    // Lirathe Phase 2: At -80 SP, take 20 true damage and lose control
    if(u.id === 'lirathe' && u._transformed && u.sp <= -80){
      damageUnit(u.id, u.spZeroHpPenalty || 20, 0, `${u.name} 因 SP 跌破 -80 受到真实伤害`, null, {trueDamage: true, ignoreCover: true, ignoreJixue: true, ignoreDepend: true});
      appendLog(`${u.name} 的 SP 跌破 -80：自动恢复至 -10`);
      u.sp = -10;
      u.spPendingRestore = null;
    } else {
      applyStunOrStack(u, 1, {bypass:true, reason:'SP崩溃'});
      if(u.side==='player'){ playerSteps = Math.max(0, playerSteps - 1); } else { enemySteps = Math.max(0, enemySteps - 1); }
      const restored = Math.floor(u.maxSp * u.restoreOnZeroPct);
      u.spPendingRestore = Math.max(u.spPendingRestore ?? 0, restored);
      appendLog(`${u.name} 的 SP 崩溃：下个己方回合自动恢复至 ${u.spPendingRestore}`);
    }
  }
  if(u.sp > spCrashThreshold && u._spBroken) u._spBroken = false;
  if(u.sp > spCrashThreshold){
    refreshSpCrashVulnerability(u);
  }
}
function applySpDamage(targetOrId, amount, {sourceId=null, reason=null}={}){
  const u = typeof targetOrId === 'string' ? units[targetOrId] : targetOrId;
  if(!u || u.hp<=0 || amount<=0) return 0;
  const before = u.sp;
  const minSp = u.minSp !== undefined ? u.minSp : 0;
  u.sp = Math.max(minSp, u.sp - amount);
  const delta = before - u.sp;
  if(delta>0){
    showDamageFloat(u,0,delta);
    if(reason){ appendLog(reason.replace('{delta}', String(delta))); }
    handleSpCrashIfNeeded(u);
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
function hasBloomInAnyPlayerPool(){
  // Check if any player has the Bloom skill in their pool
  for(const id of ['adora','dario','karma']){
    const u = units[id];
    if(!u || u.hp<=0) continue;
    const pool = u.skillPool || [];
    if(pool.some(s=>s && s.name === '绽放（红色）')) return true;
  }
  return false;
}
function calcOutgoingDamage(attacker, baseDmg, target, skillName){
  let dmg = baseDmg;
  if(attacker.passives.includes('fearBuff') && attacker.sp<10) dmg = Math.round(dmg*1.5);
  if(attacker.passives.includes('pride')){
    const lostRatio = (attacker.maxHp - attacker.hp) / attacker.maxHp;
    dmg = Math.round(dmg * (1 + lostRatio * 0.5));
  }
  if(attacker.id==='karma' && skillName==='沙包大的拳头' && (attacker.consecAttacks||0)>=1){ dmg = Math.round(dmg*1.5); }
  if((attacker.id==='adora' || attacker.id==='adora_phantom') && skillName==='短匕轻挥' && target){ dmg = Math.round(dmg * backstabMultiplier(attacker,target)); }
  if(attacker.team==='seven'){ dmg = Math.max(0, dmg - 5); }
  if(attacker.id==='haz' && attacker.hp <= attacker.maxHp/2){ dmg = Math.round(dmg * 1.3); }
  if(attacker.id==='haz' && attacker._comeback) dmg = Math.round(dmg * 1.10);

  if(hasDeepBreathPassive(attacker)){
    dmg = Math.round(dmg * 1.10);
  }

  const withinCritWindow = roundsPassed <= 15;
  if(attacker.team==='seven' && withinCritWindow && Math.random() < 0.30){ dmg = Math.round(dmg * 1.5); appendLog(`${attacker.name} 暴击！伤害 x1.5`); }

  if(attacker.team==='seven' && target && hazMarkedTargetId && target.id===hazMarkedTargetId){ dmg = Math.round(dmg * 1.15); }
  if(attacker.id==='tusk' && (attacker.tuskRageStacks||0)>0){ dmg += 5*attacker.tuskRageStacks; appendLog(`Tusk 猛牛之力：额外 +${5*attacker.tuskRageStacks} 伤害`); attacker.tuskRageStacks = 0; }
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

    // 灵活Buff - 30%几率miss攻击
    if(!opts.ignoreMiss && u.status && u.status.agileStacks > 0 && Math.random() < 0.30){
      appendLog(`${u.name} 的"灵活"触发：${source.name} 的攻击Miss！`);
      updateStatusStacks(u,'agileStacks', Math.max(0, u.status.agileStacks - 1), {label:'灵活', type:'buff'});
      showStatusFloat(u,'Miss',{type:'buff', offsetY:-48});
      pulseCell(u.r,u.c);
      renderAll();
      return;
    }

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
        source._dependTarget = u; // Store the target for stun application
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
  // 力挽狂澜减伤
  if(u.id==='haz' && u._comeback && !trueDamage){
    hpDmg = Math.round(hpDmg * 0.9);
    spDmg = Math.round(spDmg * 0.9);
  }

  // 姿态减伤（优先于 Tusk 固有护甲）
  if(!trueDamage && u._stanceType && u._stanceTurns>0 && u._stanceDmgRed>0){
    hpDmg = Math.round(hpDmg * (1 - u._stanceDmgRed));
    spDmg = Math.round(spDmg * (1 - u._stanceDmgRed));
  } else {
    // Tusk 固有“骨墙”（若未进入姿态）
    if(!trueDamage && u.id==='tusk' && !opts.ignoreTuskWall){
      hpDmg = Math.round(hpDmg * 0.7);
      spDmg = Math.round(spDmg * 0.7);
    }
  }

  // Tusk 替 Haz 承伤
  if(!trueDamage && u.id==='haz'){
    const tusk = units['tusk'];
    if(tusk && tusk.hp>0){
      const redHp = Math.round(hpDmg * 0.5);
      const redSp = Math.round(spDmg * 0.5);
      appendLog(`Tusk 家人的守护：替 Haz 承受伤害（-50%）`);
      tusk.tuskRageStacks = (tusk.tuskRageStacks||0) + 1;
      damageUnit('tusk', redHp, redSp, `（转移自 Haz）${reason}`, sourceId, {...opts, _redirected:true});
      return;
    }
  }

  if(!trueDamage && u.id==='haz' && u.chainShieldTurns>0){
    hpDmg = Math.round(hpDmg * 0.6);
    spDmg = Math.round(spDmg * 0.6);
  }
  if(!trueDamage && u.passives.includes('toughBody') && !opts.ignoreToughBody){
    hpDmg = Math.round(hpDmg * 0.75);
  }
  
  if(!trueDamage && u.side === "player"){
    const equipped = loadEquippedAccessories();
    if(equipped[u.id] === "vest"){
      hpDmg = Math.round(hpDmg * 0.8);
    }
  }

  if(u._spCrashVuln && (hpDmg>0 || spDmg>0)){
    hpDmg = Math.round(hpDmg * 2);
    spDmg = Math.round(spDmg * 2);
    appendLog(`${u.name} 因 SP 崩溃眩晕承受双倍伤害！`);
  }
  
  // Lirathe weakness vulnerability from stepping on weakness tile
  if(u._weaknessVulnerable && (hpDmg>0 || spDmg>0)){
    hpDmg = Math.round(hpDmg * 1.5);
    spDmg = Math.round(spDmg * 1.5);
    appendLog(`${u.name} 因软肋承受额外伤害！`);
  }

  const prevHp = u.hp;
  let finalHp = Math.max(0, hpDmg);
  let finalSp = Math.max(0, spDmg);

  // 肯定Buff - 免疫SP伤害（多阶段攻击全阶段免疫）
  if(!opts.ignoreAffirmation && finalSp > 0 && u.status && u.status.affirmationStacks > 0){
    appendLog(`${u.name} 的"肯定"触发：免疫本次SP伤害`);
    updateStatusStacks(u,'affirmationStacks', Math.max(0, u.status.affirmationStacks - 1), {label:'肯定', type:'buff'});
    showStatusFloat(u,'SP免疫',{type:'buff', offsetY:-48});
    finalSp = 0;
  }

  u.hp = Math.max(0, u.hp - finalHp);
  const minSp = u.minSp !== undefined ? u.minSp : 0;
  u.sp = Math.max(minSp, u.sp - finalSp);
  
  // Lock Karma to minimum HP during final phase
  if(u._lockedMinHp !== undefined && u.hp < u._lockedMinHp){
    u.hp = u._lockedMinHp;
  }
  
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
  if(died){
    showDeathFx(u);
    handleUnitDeath(u, source);
  }

  // 锁链缠绕 反击（Haz）
  if(sourceId){
    const src = units[sourceId];
    if(src && u.chainShieldTurns>0 && u.chainShieldRetaliate>0){
      u.chainShieldRetaliate = 0;
      applySpDamage(src, 10, {sourceId: u.id, reason:`锁链缠绕反击：${src.name} SP -{delta}`});
      showSkillFx('haz:锁链缠绕·反击',{target:src});
    }
  }

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
  
  // Dario 反击 passive: 50% chance to counter with 机械爪击
  if(sourceId && (u.id==='dario' || u.id==='dario_phantom') && u.passives.includes('counterattack') && !opts._counterattack){
    if(Math.random() < 0.5){
      const src = units[sourceId];
      if(src && src.hp>0 && src.side!==u.side){
        appendLog(`${u.name} 的"反击"触发：反击一次机械爪击`);
        setTimeout(()=>{
          if(src.hp > 0){
            darioClaw(u, src);
          }
        }, 300);
      }
    }
  }

  if(sourceId){
    const src = units[sourceId];
    if(src && src.side === "player" && (finalHp>0 || finalSp>0)){
      const equipped = loadEquippedAccessories();
      if(equipped[src.id] === "tetanus"){
        const currentBleed = u.status.bleed || 0;
        u.status.bleed = currentBleed + 1;
        updateStatusStacks(u, "bleed", u.status.bleed, { label: "流血", type: "debuff" });
          addStatusStacks(u, "resentStacks", 1, { label: "怨念", type: "debuff" });
        appendLog(`${src.name} 的"破伤风之刃"：${u.name} +1 流血 +1 怨念`);
      }
      // Bloom (Red) passive: Stack Bloody Bud when any player deals damage to enemies
      if(u.side !== src.side && hasBloomInAnyPlayerPool()){
        const currentBuds = u.status.bloodyBud || 0;
        if(currentBuds < 7){
          updateStatusStacks(u, "bloodyBud", currentBuds + 1, { label: "血色花蕾", type: "debuff" });
          appendLog(`${src.name} 的攻击触发"绽放（红色）"被动：${u.name} +1 层血色花蕾 (${currentBuds + 1}/7)`);
        }
      }
    }
  }

  handleSpCrashIfNeeded(u);
  checkHazComebackStatus();
  
  // 意识花苞：记录受伤回合（用于恢复被动）
  if(u.passives && u.passives.includes('recovery') && (finalHp > 0 || finalSp > 0)){
    u._lastDamagedRound = roundsPassed;
  }
  
  // Lirathe HP≤400 Final Phase trigger
  if(u.id === 'lirathe' && u._transformed && u.hp <= 400 && u.hp > 0 && !u._finalPhaseTriggered){
    u._finalPhaseTriggered = true;
    setTimeout(()=> triggerLiratheFinalPhase(), 500);
  }

  renderAll();
}

function handleUnitDeath(u, source){
  if(!u) return;
  
  // 意识花苞死后创建"软肋"格子
  if(u.id && u.id.startsWith('consciousness_')){
    createWeaknessTile(u.r, u.c);
    appendLog(`${u.name} 死后，格子变为"软肋"格子`);
  }
  
  // Lirathe Phase 1 → Phase 2 transformation
  if(u.id === 'lirathe' && !u._transformed && u.hp <= 0){
    u.hp = 1; // Prevent actual death
    u._transformed = true;
    u.maxHp = 1200;
    u.hp = 1200;
    u.maxSp = 0;
    u.sp = -10;
    u.minSp = -80; // Lirathe Phase 2 can go to -80 SP
    u.restoreOnZeroPct = 0;
    u.spZeroHpPenalty = 20;
    u.spCrashThreshold = -80; // Changed from 0 to -80
    
    // Clear skill pool, force redraw Phase 2 skills
    u.skillPool = [];
    u.dealtStart = false;
    ensureStartHand(u);
    
    appendLog('=====================');
    appendLog('Lirathe 进入第二阶段！');
    appendLog('变身后的Lirathe失去了视力，但听觉敏锐！');
    appendLog('=====================');
    
    // Start consciousness flower and healing tile timers
    u._consciousnessFlowerRounds = 0;
    u._healingTileRounds = 0;
    
    renderAll();
    return; // Don't process normal death
  }
  
  if(u.id === 'haz' && !hazTeamCollapsed){
    hazTeamCollapsed = true;
    appendLog('Haz 倒下，七海作战队群龙无首！其余成员全数溃散。');
    for(const id in units){
      const ally = units[id];
      if(!ally || ally === u) continue;
      if(ally.side === 'enemy' && ally.team === 'seven' && ally.hp > 0){
        const hpDmg = ally.hp;
        const spDmg = ally.sp;
        damageUnit(ally.id, hpDmg, spDmg, `Haz 陨落，${ally.name} 无力再战`, null, {
          trueDamage: true,
          ignoreCover: true,
          ignoreToughBody: true,
          ignoreMiss: true,
          ignoreAffirmation: true,
          ignoreJixue: true,
          ignoreDepend: true,
          ignoreTuskWall: true,
        });
      }
    }
  }
}

// —— 公用 FX ——
function showTrailWithDuration(r1,c1,r2,c2,duration=500,{thickness=6,color=null}={}){
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
  onAnimEndRemove(trail, duration);
}
function showTrail(r1,c1,r2,c2,{thickness=6,color=null}={}){
  showTrailWithDuration(r1,c1,r2,c2,260,{thickness,color});
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
function darioTearWound(u, target){
  if(!target || target.side===u.side){ appendLog('撕裂伤口 目标无效'); return; }

  const isFullHp = target.hp >= target.maxHp;
  let dmg = 15;

  if(!isFullHp){
    dmg = Math.round(dmg * 1.5);
    appendLog(`${target.name} 非满血，撕裂伤口 伤害增加 50%`);
  }

  const finalDmg = calcOutgoingDamage(u, dmg, target, '撕裂伤口');
  cameraFocusOnCell(target.r, target.c);

  damageUnit(target.id, finalDmg, 0, `${u.name} 用 撕裂伤口 爪击 ${target.name}`, u.id, {skillFx:'dario:撕裂伤口'});
  u.dmgDone += finalDmg;

  const bleedStacks = isFullHp ? 1 : 2;
  addStatusStacks(target, 'bleed', bleedStacks, {label:'流血', type:'debuff'});
  appendLog(`${target.name} 附加 流血+${bleedStacks}`);

  setTimeout(() => {
    if(target.hp > 0){
      const dmg2 = calcOutgoingDamage(u, 5, target, '撕裂伤口');
      damageUnit(target.id, dmg2, 0, `${u.name} 抽出利爪`, u.id, {skillFx:'dario:撕裂伤口'});
      u.dmgDone += dmg2;
    }
  }, 400);
}
function darioStatusRecovery(u, aim){
  const t = getUnitAt(aim.r, aim.c);
  if(!t || t.side!==u.side){ appendLog('状态恢复 目标无效'); return; }

  const clearedEffects = [];
  if(t.status.stunned > 0){ clearedEffects.push('眩晕'); t.status.stunned = 0; }
  if(t.status.paralyzed > 0){ clearedEffects.push('恐惧'); t.status.paralyzed = 0; }
  if(t.status.bleed > 0){ clearedEffects.push('流血'); t.status.bleed = 0; }
  if(t.status.hazBleedTurns > 0){ clearedEffects.push('Haz流血'); t.status.hazBleedTurns = 0; }

  const spBefore = t.sp;
  t.sp = Math.min(t.maxSp, t.sp + 15);
  syncSpBroken(t);

  pulseCell(t.r, t.c);
  showSkillFx('dario:状态恢复', {target:t});

  if(clearedEffects.length > 0){
    appendLog(`${u.name} 对 ${t.name} 使用 状态恢复：清除 ${clearedEffects.join('、')}，恢复 15SP`);
  } else {
    appendLog(`${u.name} 对 ${t.name} 使用 状态恢复：恢复 15SP（无负面效果需清除）`);
  }
  showGainFloat(t, 0, t.sp - spBefore);

  unitActed(u);
}
async function adoraAssassination(u, target){
  if(!target || target.side===u.side || target.hp<=0){ 
    appendLog('课本知识：刺杀一 目标无效'); 
    unitActed(u); 
    return; 
  }
  
  // Get position behind target
  const targetDir = cardinalDirFromDelta(target.r - u.r, target.c - u.c);
  const behindCell = forwardCellAt(target, targetDir, 1);
  
  // If can't get behind, just attack from current position
  const teleportDest = behindCell && !getUnitAt(behindCell.r, behindCell.c) ? behindCell : null;
  
  // Stage 1: Teleport and stab in
  if(teleportDest){
    const origR = u.r, origC = u.c;
    // Show blade flash trail from original position to destination (0.5 seconds)
    showTrailWithDuration(origR, origC, teleportDest.r, teleportDest.c, 500, {thickness: 8, color: 'rgba(196, 69, 105, 0.85)'});
    await sleep(200);
    u.r = teleportDest.r;
    u.c = teleportDest.c;
    pulseCell(u.r, u.c);
    const newDir = cardinalDirFromDelta(target.r - u.r, target.c - u.c);
    setUnitFacing(u, newDir);
    appendLog(`${u.name} 瞬移到 ${target.name} 后侧`);
    await sleep(300);
  }
  
  await telegraphThenImpact([{r:target.r,c:target.c}]);
  cameraFocusOnCell(target.r, target.c);
  const dmg1 = calcOutgoingDamage(u, 10, target, '课本知识：刺杀一');
  damageUnit(target.id, dmg1, 5, `${u.name} 匕首插入 ${target.name}`, u.id, {skillFx:'adora:课本知识：刺杀一'});
  u.dmgDone += dmg1;
  await sleep(600);
  
  // Stage 2: Pull out and apply bleed
  if(target.hp > 0){
    await telegraphThenImpact([{r:target.r,c:target.c}]);
    const dmg2 = calcOutgoingDamage(u, 5, target, '课本知识：刺杀一');
    damageUnit(target.id, dmg2, 5, `${u.name} 拔出匕首 ${target.name}`, u.id, {skillFx:'adora:课本知识：刺杀一'});
    u.dmgDone += dmg2;
    const bleedStacks = addStatusStacks(target, 'bleed', 1, {label:'流血', type:'debuff'});
    appendLog(`${target.name} 流血层数 -> ${bleedStacks}`);
  }
  
  unitActed(u);
}
function adoraBloom(u){
  // Bloom all Bloody Buds on the field
  cameraFocusOnCell(u.r, u.c);
  let totalBloomedTargets = 0;
  let totalLayersDetonated = 0;
  
  // Find all enemies with Bloody Bud stacks
  for(const id in units){
    const target = units[id];
    if(!target || target.hp<=0 || target.side===u.side) continue;
    const budStacks = target.status.bloodyBud || 0;
    if(budStacks > 0){
      totalBloomedTargets++;
      totalLayersDetonated += budStacks;
      // Calculate true damage: 10 HP + 5 SP per stack
      const hpDmg = budStacks * 10;
      const spDmg = budStacks * 5;
      
      // Apply true damage
      damageUnit(target.id, hpDmg, spDmg, `${u.name} 的 绽放（红色） 引爆了 ${target.name} 的 ${budStacks} 层血色花蕾`, u.id, {
        trueDamage: true,
        skillFx: 'adora:绽放（红色）·爆裂',
        skillFxCtx: {target: target}
      });
      
      // Clear Bloody Bud stacks
      updateStatusStacks(target, 'bloodyBud', 0, {label: '血色花蕾', type: 'debuff'});
      
      u.dmgDone += hpDmg;
    }
  }
  
  let adoraHpGained = 0;
  let adoraSpGained = 0;
  const healedAllies = [];

  if(totalLayersDetonated > 0){
    const rangeLimit = 5;
    for(const id in units){
      const ally = units[id];
      if(!ally || ally.hp <= 0 || ally.side !== u.side) continue;
      if(ally.id !== u.id && mdist(u, ally) > rangeLimit) continue;

      let hpHeal = totalLayersDetonated * 3;
      let spHeal = totalLayersDetonated * 3;
      if(ally.id === u.id){
        hpHeal += totalLayersDetonated * 5;
        spHeal += totalLayersDetonated * 5;
      }
      if(hpHeal <= 0 && spHeal <= 0) continue;

      const prevHp = ally.hp;
      const prevSp = ally.sp;
      ally.hp = Math.min(ally.maxHp, ally.hp + hpHeal);
      ally.sp = Math.min(ally.maxSp, ally.sp + spHeal);
      syncSpBroken(ally);
      const gainedHp = ally.hp - prevHp;
      const gainedSp = ally.sp - prevSp;
      if(gainedHp > 0 || gainedSp > 0){
        showGainFloat(ally, gainedHp, gainedSp);
        showSkillFx('adora:绽放（红色）·治疗', {target: ally});
        if(ally.id === u.id){
          adoraHpGained += gainedHp;
          adoraSpGained += gainedSp;
        } else {
          healedAllies.push({name: ally.name, hp: gainedHp, sp: gainedSp});
        }
      }
    }
  }

  if(totalBloomedTargets === 0){
    appendLog(`${u.name} 使用了 绽放（红色），但场上没有血色花蕾`);
  } else {
    const alliesDetail = healedAllies.length
      ? `；范围治疗 ${healedAllies.map(h => `${h.name}(+${h.hp}HP/+${h.sp}SP)`).join('、')}`
      : '';
    appendLog(`${u.name} 使用 绽放（红色），引爆了 ${totalBloomedTargets} 个敌人的血色花蕾（共 ${totalLayersDetonated} 层），自身恢复 ${adoraHpGained} HP 和 ${adoraSpGained} SP${alliesDetail}`);
  }

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
  appendLog(`${u.name} 对 ${t.name} 施加“依赖”：下一次攻击造成真实伤害、叠加2层眩晕层数、清空SP、消耗1层依赖`);
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
  if(u.consecAttacks > 0){ appendLog(`${u.name} 的连击被打断（移动）`); u.consecAttacks = 0; }
  u.sp = Math.min(u.maxSp, u.sp + 5); syncSpBroken(u); showGainFloat(u,0,5);
  unitActed(u);
}
function karmaGrip(u,target){
  if(!target || target.side===u.side){ appendLog('嗜血之握 目标无效'); return; }
  cameraFocusOnCell(target.r, target.c);
  let fixed = null;
  if(target.id==='haz') fixed = 75;
  else if(target.id==='tusk' || target.id==='katz') fixed = 80;
  else if(target.id==='kyn' || target.id==='neyla') fixed = 100;
  // Add support for heresy enemies
  if(target.id==='khathia') fixed = 75;
  if(target.id==='heresy_boss_b') fixed = 80;
  if(target.id && target.id.startsWith('heresy_elite_')) fixed = 100;
  if(fixed!==null){
    const deal = Math.min(target.hp, fixed);
    damageUnit(target.id, deal, 0, `${u.name} 嗜血之握 重创 ${target.name}`, u.id, {trueDamage:true, ignoreTuskWall:true, skillFx:'karma:嗜血之握'});
  } else {
    // Normal enemies - execute with true damage
    damageUnit(target.id, target.hp, 0, `${u.name} 嗜血之握 处决 ${target.name}`, u.id, {trueDamage:true, ignoreTuskWall:true, skillFx:'karma:嗜血之握'});
  }
  unitActed(u);
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
        updateStatusStacks(u,'dependStacks', prev - 1, {label:'依赖', type:'buff'});
        const beforeSp = u.sp;
        u.sp = 0;
        // Add 2 layers of stun stacks to the target instead of the source
        const target = u._dependTarget;
        if(target && target.id && target.hp > 0){
          applyStunOrStack(target, 2, {reason:'依赖触发'});
        }
        if(beforeSp>0){
          appendLog(`${u.name} 的"依赖"触发：SP 清空，给目标叠加 2 层眩晕层数，消耗 1 层依赖`);
          showDamageFloat(u,0,beforeSp);
        } else {
          appendLog(`${u.name} 的"依赖"触发：SP 已为 0，给目标叠加 2 层眩晕层数，消耗 1 层依赖`);
        }
        handleSpCrashIfNeeded(u);
        syncSpBroken(u);
        requireFullRender = true;
      }
    }
    u._dependUnleash = false;
    u._dependTarget = null; // Clear the target reference
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
  u.dmgDone += dmg;
  u.consecAttacks = (u.consecAttacks||0)+1;

  const adrenalineSkill = (u.skillPool || []).find(s => s && s.name === '肾上腺素' && !s._used);
  if(adrenalineSkill && u.consecAttacks >= 2 && u.consecAttacks % 2 === 0){
    appendLog(`${u.name} 的"肾上腺素"被动触发：连续攻击2次后自动再次攻击！`);
    setTimeout(() => {
      if(target.hp > 0){
        const dmg1 = calcOutgoingDamage(u, 15, target, '沙包大的拳头');
        damageUnit(target.id, dmg1, 0, `${u.name} 肾上腺素连击1`, u.id,{skillFx:'karma:沙包大的拳头'});
        u.dmgDone += dmg1;

        setTimeout(() => {
          if(target.hp > 0){
            const dmg2 = calcOutgoingDamage(u, 15, target, '沙包大的拳头');
            damageUnit(target.id, dmg2, 0, `${u.name} 肾上腺素连击2`, u.id,{skillFx:'karma:沙包大的拳头'});
            u.dmgDone += dmg2;
          }
        }, 400);
      }
    }, 400);
  }

  unitActed(u);
}

// —— Katz 技能（含新反复鞭尸逻辑） —— 
async function katz_RepeatedWhip(u, desc){
  // 反复鞭尸（三步）
  // 鱼矛成鞭，挥舞前面3格所有敌方单位：10伤害后再15伤害，并恢复5SP；
  // 按自身SP百分比重复该两段攻击（floor(sp/maxSp*5) 次，1..5），最多5次
  const dir = (desc && desc.dir) ? desc.dir : u.facing;
  const cells = range_forward_n(u,3,dir);
  if(!cells.length){ appendLog('反复鞭尸：前路受阻'); unitActed(u); return; }

  const cycles = Math.max(1, Math.min(5, Math.floor((u.sp / Math.max(1,u.maxSp)) * 5)));
  let totalHits = 0;
  for(let cycle=1; cycle<=cycles; cycle++){
    await telegraphThenImpact(cells);
    const hitSet1=new Set(); let hits1=0;
    for(const c of cells){
      const tu=getUnitAt(c.r,c.c);
      if(tu && tu.side!=='enemy' && !hitSet1.has(tu.id)){
        damageUnit(tu.id, 10, 0, `${u.name} 反复鞭尸·第${cycle}次 第一鞭 命中 ${tu.name}`, u.id,{skillFx:'katz:反复鞭尸'});
        hitSet1.add(tu.id); hits1++;
      }
    }
    await stageMark(cells);
    const hitSet2=new Set(); let hits2=0;
    for(const c of cells){
      const tu=getUnitAt(c.r,c.c);
      if(tu && tu.side!=='enemy' && !hitSet2.has(tu.id)){
        damageUnit(tu.id, 15, 0, `${u.name} 反复鞭尸·第${cycle}次 第二鞭 重击 ${tu.name}`, u.id,{skillFx:'katz:反复鞭尸'});
        hitSet2.add(tu.id); hits2++;
      }
    }
    // 每轮 +5SP
    const beforeSP = u.sp;
    u.sp = Math.min(u.maxSp, u.sp + 5);
    syncSpBroken(u);
    showGainFloat(u,0,u.sp-beforeSP);
    totalHits += hits1 + hits2;
  }
  appendLog(`反复鞭尸 累计命中段数：${totalHits}`);
  unitActed(u);
}
async function katz_EndSalvo(u, desc){
  // 终焉礼炮：直线5格，每单位35HP（不受掩体）；常态/压迫均可用
  const dir = (desc && desc.dir) ? desc.dir : u.facing;
  const cells = range_forward_n(u,5,dir);
  await telegraphThenImpact(cells);
  let hits=0,set=new Set();
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !set.has(tu.id)){
      damageUnit(tu.id, 35, 0, `${u.name} 终焉礼炮 命中 ${tu.name}`, u.id, {ignoreCover:true, skillFx:'katz:终焉礼炮'});
      set.add(tu.id); hits++;
    }
  }
  appendLog(`终焉礼炮 命中 ${hits} 人`);
  unitActed(u);
}

// —— 新增技能实现 —— 
// Adora：略懂的医术！（25级，粉色）
function adoraFieldMedic(u, aim){
  const t = getUnitAt(aim.r, aim.c);
  if(!t || t.side!==u.side){ appendLog('略懂的医术！ 目标无效'); return; }
  const hpBefore = t.hp, spBefore = t.sp;
  t.hp = Math.min(t.maxHp, t.hp + 20);
  t.sp = Math.min(t.maxSp, t.sp + 15);
  syncSpBroken(t);
  const stacks = addStatusStacks(t,'recoverStacks',1,{label:'恢复', type:'buff'});
  appendLog(`${u.name} 对 ${t.name} 使用 略懂的医术！：+20HP +15SP，并赋予“恢复”(${stacks})`);
  showGainFloat(t,t.hp-hpBefore,t.sp-spBefore);
  showSkillFx('adora:略懂的医术！',{target:t});
  unitActed(u);
}
// Karma：深呼吸（25级，白色）
function karmaDeepBreath(u){
  const hpBefore = u.hp, spBefore = u.sp;
  u.sp = u.maxSp; syncSpBroken(u);
  u.hp = Math.min(u.maxHp, u.hp + 10);
  appendLog(`${u.name} 使用 深呼吸：SP回满，+10HP（被动+10%仅在手牌中未被使用时生效）`);
  showGainFloat(u,u.hp-hpBefore,u.sp-spBefore);
  showSkillFx('karma:深呼吸',{target:u});
  unitActed(u);
}
function karmaAdrenaline(u){
  updateStatusStacks(u, 'jixueStacks', 1, {label:'鸡血', type:'buff'});

  const hpBefore = u.hp, spBefore = u.sp;
  u.hp = Math.min(u.maxHp, u.hp + 15);
  u.sp = Math.min(u.maxSp, u.sp + 5);
  syncSpBroken(u);

  appendLog(`${u.name} 使用 肾上腺素：获得 鸡血+1，恢复 15HP 与 5SP`);
  showGainFloat(u, u.hp-hpBefore, u.sp-spBefore);
  showSkillFx('karma:肾上腺素', {target:u});

  const adrenalineSkill = (u.skillPool || []).find(s => s && s.name === '肾上腺素');
  if(adrenalineSkill){ adrenalineSkill._used = true; }

  unitActed(u);
}

// Haz 原有与禁招（多阶段均即时结算）
async function haz_HarpoonStab(u, target){
  if(!target || target.side===u.side){ appendLog('鱼叉穿刺 目标无效'); return; }
  const cells=[{r:target.r,c:target.c}];
  await telegraphThenImpact(cells);
  const dmg = calcOutgoingDamage(u,20,target,'鱼叉穿刺');
  cameraFocusOnCell(target.r, target.c);
  damageUnit(target.id, dmg, 0, `${u.name} 鱼叉穿刺 命中 ${target.name}`, u.id,{skillFx:'haz:鱼叉穿刺'});
  u.sp = Math.min(u.maxSp, u.sp + 10); syncSpBroken(u); showGainFloat(u,0,10);
  if(!hazMarkedTargetId){ hazMarkedTargetId = target.id; appendLog(`猎杀标记：${target.name} 被标记，七海对其伤害 +15%`); }
  if(Math.random() < 0.4){
    const reduced = applySpDamage(target,5,{sourceId:u.id});
    appendLog(`${target.name} SP -${reduced}（恐惧）`);
    addStatusStacks(target,'paralyzed',1,{label:'恐惧', type:'debuff'});
    appendLog(`${target.name} 下回合 -1 步`);
    showSkillFx('haz:怨念滋生·恐惧',{target:target});
  }
  u.dmgDone += dmg; unitActed(u);
}
async function haz_DeepHunt(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  const cells = range_forward_n(u,3,dir);
  await telegraphThenImpact(cells);
  let target=null;
  for(const c of cells){ const tu=getUnitAt(c.r,c.c); if(tu && tu.side!=='enemy'){ target=tu; break; } }
  if(!target){ appendLog('深海猎杀 未找到目标'); return; }
  const dmg = calcOutgoingDamage(u,25,target,'深海猎杀');
  cameraFocusOnCell(target.r, target.c);
  damageUnit(target.id, dmg, 0, `${u.name} 深海猎杀 命中 ${target.name}`, u.id,{skillFx:'haz:深海猎杀'});
  const front = forwardCellAt(u, dir, 1);
  if(front && !getUnitAt(front.r, front.c)){ target.r = front.r; target.c = front.c; pulseCell(front.r, front.c); appendLog(`${target.name} 被拉至面前一格`); }
  const reduced = applySpDamage(target,10,{sourceId:u.id});
  appendLog(`${target.name} SP -${reduced}`);
  if(!hazMarkedTargetId){ hazMarkedTargetId = target.id; appendLog(`猎杀标记：${target.name} 被标记，七海对其伤害 +15%`); }
  u.dmgDone += dmg; unitActed(u);
}
async function haz_GodFork(u, target){
  if(!target || target.side===u.side){ appendLog('猎神之叉 目标无效'); return; }
  await telegraphThenImpact([{r:target.r,c:target.c}]);
  const adj = range_adjacent(target);
  let dest = null, best=1e9;
  for(const p of adj){ if(getUnitAt(p.r,p.c)) continue; const d = mdist(u, p); if(d<best){best=d; dest=p;} }
  if(dest){ u.r=dest.r; u.c=dest.c; pulseCell(u.r,u.c); appendLog(`${u.name} 瞬移至 ${target.name} 身边`); }
  let dmg = calcOutgoingDamage(u,20,target,'猎神之叉');
  if(Math.random()<0.5){ dmg = Math.round(dmg*2.0); appendLog('猎神之叉 暴怒加成 x2.0'); }
  cameraFocusOnCell(target.r, target.c);
  damageUnit(target.id, dmg, 15, `${u.name} 猎神之叉 重击 ${target.name}`, u.id,{skillFx:'haz:猎神之叉'});
  const bleedStacks = Math.max(target.status.bleed||0, 2);
  updateStatusStacks(target,'bleed', bleedStacks,{label:'流血', type:'debuff'});
  appendLog(`${target.name} 附加流血（2回合，每回合 -5%最大HP）`);
  if(!hazMarkedTargetId){ hazMarkedTargetId = target.id; appendLog(`猎杀标记：${target.name} 被标记，七海对其伤害 +15%`); }
  u.dmgDone += dmg; unitActed(u);
}
function haz_ChainShield(u){
  u.chainShieldTurns = 2; u.chainShieldRetaliate = 1;
  appendLog(`${u.name} 锁链缠绕：2回合内伤害-40%，下次被打反击 10SP`);
  showSkillFx('haz:锁链缠绕',{target:u});
  for(const id in units){
    const v=units[id];
    if(v.team==='seven' && v.hp>0){
      v.sp = Math.min(v.maxSp, v.sp+5);
      syncSpBroken(v);
      showGainFloat(v,0,5);
      showSkillFx('haz:锁链缠绕·增益',{target:v});
    }
  }
  unitActed(u);
}
async function haz_WhaleFall(u){
  const cells = range_square_n(u,2);
  await telegraphThenImpact(cells);
  const set=new Set(); let hits=0;
  for(const c of cells){
    const tu = getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !set.has(tu.id)){
      damageUnit(tu.id, 50, 20, `${u.name} 鲸落 轰击 ${tu.name}`, u.id, {ignoreCover:true, skillFx:'haz:鲸落'});
      addStatusStacks(tu,'paralyzed',1,{label:'恐惧', type:'debuff'});
      set.add(tu.id); hits++;
    }
  }
  appendLog(`鲸落 命中 ${hits} 个单位`);
  unitActed(u);
}
async function haz_PayThePrice(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;

  // 段1：前刺（前3）
  const L1 = range_forward_n(u,3,dir);
  await telegraphThenImpact(L1);
  let h1=0;
  for(const c of L1){ const tu=getUnitAt(c.r,c.c); showTrail(u.r,u.c,c.r,c.c); if(tu && tu.side!=='enemy'){ damageUnit(tu.id,15,0,`${u.name} 付出代价·前刺 命中 ${tu.name}`, u.id,{skillFx:'haz:付出代价'}); h1++; } }
  await stageMark(L1);

  // 段2：穿刺（前4）
  const L2 = range_forward_n(u,4,dir);
  await telegraphThenImpact(L2);
  let h2=0;
  for(const c of L2){ const tu=getUnitAt(c.r,c.c); showTrail(u.r,u.c,c.r,c.c); if(tu && tu.side!=='enemy'){ damageUnit(tu.id,15,5,`${u.name} 付出代价·穿刺 命中 ${tu.name}`, u.id,{skillFx:'haz:付出代价'}); h2++; } }
  await stageMark(L2);

  // 段3：横斩（横3x前2）
  const R = forwardRectCentered(u, dir, 3, 2);
  await telegraphThenImpact(R);
  let h3=0; const seen=new Set();
  for(const c of R){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      damageUnit(tu.id,15,0,`${u.name} 付出代价·横斩 命中 ${tu.name}`, u.id,{skillFx:'haz:付出代价'});
      updateStatusStacks(tu,'hazBleedTurns',2,{label:'Haz流血', type:'debuff'});
      appendLog(`${tu.name} 附加 Haz流血(2)`); seen.add(tu.id); h3++;
    }
  }
  appendLog(`付出代价：前刺${h1}/穿刺${h2}/横斩${h3}`);
  unitActed(u);
}
async function haz_ForkOfHatred(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;

  // 阶段1：横斩（横3x前2）
  const R = forwardRectCentered(u, dir, 3, 2);
  await telegraphThenImpact(R);
  let h1=0; const seen1=new Set();
  for(const c of R){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen1.has(tu.id)){
      damageUnit(tu.id,15,10,`${u.name} 仇恨之叉·横斩 命中 ${tu.name}`, u.id,{skillFx:'haz:仇恨之叉'});
      seen1.add(tu.id); h1++;
    }
  }
  await stageMark(R);

  // 阶段2：自身5x5重砸（不受掩体）
  const AOE = range_square_n(u,2);
  await telegraphThenImpact(AOE);
  let h2=0; const seen2=new Set();
  for(const c of AOE){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen2.has(tu.id)){
      damageUnit(tu.id,20,0,`${u.name} 仇恨之叉·重砸 命中 ${tu.name}`, u.id, {ignoreCover:true, skillFx:'haz:仇恨之叉'});
      updateStatusStacks(tu,'hazBleedTurns',2,{label:'Haz流血', type:'debuff'});
      appendLog(`${tu.name} 附加 Haz流血(2)`);
      seen2.add(tu.id); h2++;
    }
  }
  appendLog(`仇恨之叉：横斩命中 ${h1}，重砸命中 ${h2}`);
  unitActed(u);
}

// Katz
async function katz_Thrust(u,target){
  if(!target || target.side===u.side){ appendLog('矛刺 目标无效'); return; }
  await telegraphThenImpact([{r:target.r,c:target.c}]);
  let dmg = calcOutgoingDamage(u,20,target,'矛刺');
  cameraFocusOnCell(target.r,target.c);
  damageUnit(target.id, dmg, 0, `${u.name} 矛刺 命中 ${target.name}`, u.id,{skillFx:'katz:矛刺'});
  u.sp = Math.min(u.maxSp, u.sp+5); syncSpBroken(u); showGainFloat(u,0,5);
  u.dmgDone += dmg; unitActed(u);
}
async function katz_ChainWhip(u,desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  const cells = range_forward_n(u,3,dir);
  await telegraphThenImpact(cells);
  let hits=0, set=new Set();
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !set.has(tu.id)){
      damageUnit(tu.id,25,0,`${u.name} 链式鞭击 命中 ${tu.name}`, u.id,{skillFx:'katz:链式鞭击'});
      addStatusStacks(tu,'paralyzed',1,{label:'恐惧', type:'debuff'});
      set.add(tu.id); hits++;
    }
  }
  appendLog(`链式鞭击 命中 ${hits} 人`);
  unitActed(u);
}
async function katz_MustErase(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  const cells = range_forward_n(u,3,dir);
  await telegraphThenImpact(cells);
  const cycleTimes = Math.max(1, Math.min(5, Math.floor((u.sp/u.maxSp)*5)));
  for(let cycle=1; cycle<=cycleTimes; cycle++){
    const dmg = cycle===1?20:30;
    let set=new Set(), hits=0;
    for(const c of cells){
      const tu=getUnitAt(c.r,c.c);
      if(tu && tu.side!=='enemy' && !set.has(tu.id)){
        damageUnit(tu.id, dmg, 0, `${u.name} 必须抹杀一切.. 第${cycle}段 命中 ${tu.name}`, u.id,{skillFx:'katz:必须抹杀一切。。'});
        set.add(tu.id); hits++;
      }
    }
    if(hits>0){
      u.hp = Math.max(1, u.hp - 5); showDamageFloat(u,5,0);
      u.sp = Math.min(u.maxSp, u.sp + 5); syncSpBroken(u); showGainFloat(u,0,5);
      await stageMark(cells);
    }
  }
  unitActed(u);
}

// Tusk
async function tusk_ShieldBash(u,target){
  if(!target || target.side===u.side){ appendLog('骨盾猛击 目标无效'); return; }
  await telegraphThenImpact([{r:target.r,c:target.c}]);
  const dmg = calcOutgoingDamage(u,10,target,'骨盾猛击');
  cameraFocusOnCell(target.r,target.c);
  damageUnit(target.id, dmg, 0, `${u.name} 骨盾猛击 ${target.name}`, u.id,{skillFx:'tusk:骨盾猛击'});
  const dir = cardinalDirFromDelta(target.r-u.r, target.c-u.c);
  const back = forwardCellAt(target, dir, 1);
  if(back && !getUnitAt(back.r, back.c)){ target.r=back.r; target.c=back.c; pulseCell(back.r,back.c); appendLog(`${target.name} 被击退一格`); }
  u.dmgDone += dmg; unitActed(u);
}
async function tusk_DeepRoar(u){
  const cells = range_square_n(u,1);
  await telegraphThenImpact(cells);
  const set=new Set(); let hits=0;
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !set.has(tu.id)){
      const reduced = applySpDamage(tu, 20, {sourceId:u.id});
      appendLog(`${tu.name} 因咆哮 SP -${reduced}`);
      showSkillFx('tusk:来自深海的咆哮',{target:tu});
      set.add(tu.id); hits++;
    }
  }
  showSkillFx('tusk:来自深海的咆哮',{target:u});
  appendLog(`来自深海的咆哮 命中 ${hits} 人`);
  unitActed(u);
}
function enterStance(u, type, turns, {dmgReduction=0, spPerTurn=0, reflectPct=0}={}){
  u._stanceType = type;
  u._stanceTurns = turns;
  u._stanceDmgRed = Math.max(0, Math.min(0.9, dmgReduction));
  u._stanceSpPerTurn = Math.max(0, spPerTurn|0);
  u._reflectPct = Math.max(0, Math.min(0.9, reflectPct));
  appendLog(`${u.name} 进入${type==='defense'?'防御姿态':'反伤姿态'}（${turns}回合）`);
}
function clearStance(u){
  if(u._stanceType){
    appendLog(`${u.name} 的${u._stanceType==='defense'?'防御姿态':'反伤姿态'} 结束`);
  }
  u._stanceType=null; u._stanceTurns=0; u._stanceDmgRed=0; u._stanceSpPerTurn=0; u._reflectPct=0;
}
function tusk_WarFortress(u){
  // 防御姿态：减伤50%，每回合+10SP，3回合；期间无法移动
  enterStance(u, 'defense', 3, {dmgReduction:0.5, spPerTurn:10});
  showSkillFx('tusk:战争堡垒',{target:u});
  unitActed(u);
}
function tusk_RetaliateGuard(u){
  // 反伤姿态：减伤40%，每回合+10SP，反弹30%所受HP伤害，3回合；期间无法移动
  enterStance(u, 'retaliate', 3, {dmgReduction:0.4, spPerTurn:10, reflectPct:0.3});
  showSkillFx('tusk:拼尽全力保卫队长',{target:u});
  unitActed(u);
}
async function tusk_BullCharge(u, desc){
  // 牛鲨冲撞：朝一个方向冲锋至多3格，撞到第一个敌人时造成20伤并击退1格；若未撞到人则移动到终点
  const dir = (desc && desc.dir) ? desc.dir : u.facing;
  const path = range_forward_n(u,3,dir);
  if(!path.length){ appendLog('牛鲨冲撞：前路受阻'); unitActed(u); return; }
  await telegraphThenImpact(path);
  let lastFree = null;
  let hitTarget = null;
  for(const step of path){
    const occ = getUnitAt(step.r, step.c);
    if(occ && occ.side!=='enemy'){ hitTarget = occ; break; }
    if(!occ) lastFree = step;
    else break;
  }
  if(hitTarget){
    if(lastFree){ showTrail(u.r,u.c,lastFree.r,lastFree.c); u.r=lastFree.r; u.c=lastFree.c; pulseCell(u.r,u.c); }
    const dmg = calcOutgoingDamage(u,20,hitTarget,'牛鲨冲撞');
    cameraFocusOnCell(hitTarget.r, hitTarget.c);
    damageUnit(hitTarget.id, dmg, 0, `${u.name} 牛鲨冲撞 命中并撞击 ${hitTarget.name}`, u.id,{skillFx:'tusk:牛鲨冲撞'});
    const knockDir = cardinalDirFromDelta(hitTarget.r - u.r, hitTarget.c - u.c);
    const back = forwardCellAt(hitTarget, knockDir, 1);
    if(back && !getUnitAt(back.r, back.c)){ hitTarget.r=back.r; hitTarget.c=back.c; pulseCell(back.r, back.c); appendLog(`${hitTarget.name} 被撞退一格`); }
  } else if(lastFree){
    showTrail(u.r,u.c,lastFree.r,lastFree.c);
    u.r=lastFree.r; u.c=lastFree.c; pulseCell(u.r,u.c);
    appendLog(`${u.name} 牛鲨冲撞：无人命中，移动至终点`);
  } else {
    appendLog('牛鲨冲撞：无法前进');
  }
  unitActed(u);
}

// Neyla
async function neyla_SwiftShot(u, targetOrAim){
  let tu = null;
  if(targetOrAim){
    if(targetOrAim.id) tu = targetOrAim;
    else if(typeof targetOrAim.r==='number' && typeof targetOrAim.c==='number') tu = getUnitAt(targetOrAim.r, targetOrAim.c);
  }
  if(!tu || tu.side===u.side){ appendLog('迅捷射击 未命中'); unitActed(u); return; }
  const dist = mdist(u, tu);
  if(dist > 4){ appendLog(`${u.name} 迅捷射击 失败：目标超出射程（≤4）`); unitActed(u); return; }
  await telegraphThenImpact([{r:tu.r,c:tu.c}]);
  let base=15;
  if((u.actionsThisTurn||0)===0) base = Math.round(base*1.5);
  if(tu.hp <= tu.maxHp/2) base = base*2;
  const dmg = calcOutgoingDamage(u,base,tu,'迅捷射击');
  cameraFocusOnCell(tu.r, tu.c);
  damageUnit(tu.id, dmg, 5, `${u.name} 迅捷射击 命中 ${tu.name}`, u.id,{skillFx:'neyla:迅捷射击'});
  unitActed(u);
}
async function neyla_PierceSnipe(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  const line = range_forward_n(u,6,dir);
  await telegraphThenImpact(line);
  let hits=0, set=new Set();
  for(const c of line){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !set.has(tu.id)){
      damageUnit(tu.id,30,0,`${u.name} 穿刺狙击 命中 ${tu.name}`, u.id,{skillFx:'neyla:穿刺狙击'});
      const bleedNext = Math.max(tu.status.bleed||0, 2);
      updateStatusStacks(tu,'bleed', bleedNext,{label:'流血', type:'debuff'});
      set.add(tu.id); hits++;
    }
  }
  appendLog(`穿刺狙击 命中 ${hits} 人`);
  unitActed(u);
}
async function neyla_EndShadow(u, aim){
  const tu = getUnitAt(aim.r, aim.c);
  if(!tu || tu.side==='enemy') { appendLog('终末之影 未命中'); unitActed(u); return; }
  await telegraphThenImpact([{r:tu.r,c:tu.c}]);
  cameraFocusOnCell(tu.r, tu.c);
  damageUnit(tu.id, 50, 20, `${u.name} 终末之影 命中 ${tu.name}`, u.id,{skillFx:'neyla:终末之影'});
  unitActed(u);
}
// Neyla：双钩牵制（2步，红，前3格内优先最近，单体）
async function neyla_DoubleHook(u, desc){
  const dir = (desc && desc.dir) ? desc.dir : u.facing;
  const cells = range_forward_n(u,3,dir);
  await telegraphThenImpact(cells);
  let target=null;
  for(const c of cells){ const tu=getUnitAt(c.r,c.c); if(tu && tu.side!=='enemy'){ target=tu; break; } }
  if(!target){ appendLog('双钩牵制 未命中'); unitActed(u); return; }
  // 拉近一格
  const backDir = cardinalDirFromDelta(u.r - target.r, u.c - target.c);
  const stepCell = forwardCellAt(target, backDir, 1);
  if(stepCell && !getUnitAt(stepCell.r, stepCell.c)){
    showTrail(target.r,target.c, stepCell.r, stepCell.c);
    target.r = stepCell.r; target.c = stepCell.c; pulseCell(target.r,target.c);
    appendLog(`${target.name} 被双钩拉近一格`);
  }
  addStatusStacks(target,'paralyzed',1,{label:'恐惧', type:'debuff'});
  appendLog(`${target.name} 因双钩牵制：下回合 -1 步`);
  const dmg = calcOutgoingDamage(u,15,target,'双钩牵制');
  damageUnit(target.id, dmg, 0, `${u.name} 双钩牵制 命中 ${target.name}`, u.id,{skillFx:'neyla:双钩牵制'});
  showSkillFx('neyla:双钩牵制',{target:target});
  u.dmgDone += dmg; unitActed(u);
}

async function neyla_ExecuteHarpoons(u, desc){
  const dir = (desc && desc.dir) ? desc.dir : u.facing;
  const line = range_line(u, dir);
  if(line.length===0){ appendLog('执行……：前方没有可以射击的目标'); unitActed(u); return; }
  await telegraphThenImpact(line);
  const targets=[]; const seen=new Set();
  for(const cell of line){
    const tu = getUnitAt(cell.r, cell.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      targets.push(tu);
      seen.add(tu.id);
    }
  }
  if(targets.length>0){ cameraFocusOnCell(targets[0].r, targets[0].c); }
  const applySelfCost = (hpCost, spCost, stageLabel)=>{
    let lostHp = 0;
    if(hpCost>0 && u.hp>0){
      const before = u.hp;
      u.hp = Math.max(0, u.hp - hpCost);
      lostHp = before - u.hp;
      if(lostHp>0){
        appendLog(`${u.name} ${stageLabel} 反噬：HP -${lostHp}`);
        showDamageFloat(u, lostHp, 0);
        pulseCell(u.r, u.c);
        if(before>0 && u.hp<=0){ showDeathFx(u); }
      }
    }
    if(spCost>0){
      applySpDamage(u, spCost, {reason:`${u.name} ${stageLabel} 反噬：SP -{delta}`});
    }
    if(lostHp>0){ renderAll(); }
    return {lostHp};
  };

  let firstHits = 0;
  for(const target of targets){
    if(target.hp<=0) continue;
    const dmg = calcOutgoingDamage(u,20,target,'执行……·第一枪');
    damageUnit(target.id, dmg, 0, `${u.name} 执行……·第一枪 命中 ${target.name}`, u.id,{skillFx:'neyla:执行……'});
    u.dmgDone += dmg;
    firstHits++;
  }
  if(firstHits>0){ appendLog(`执行……·第一枪 命中 ${firstHits} 人`); }
  else { appendLog('执行……·第一枪 未命中任何目标'); }
  applySelfCost(15, 0, '第一枪');
  await stageMark(line);
  if(u.hp<=0){ unitActed(u); return; }
  await sleep(180);

  let secondHits = 0; let executeCount = 0;
  for(const target of targets){
    if(target.hp<=0) continue;
    const executeThreshold = Math.ceil(target.maxHp * 0.15);
    if(target.hp <= executeThreshold){
      const lethal = target.hp;
      damageUnit(target.id, lethal, 0, `${u.name} 执行……·第二枪 处决 ${target.name}`, u.id,{skillFx:'neyla:执行……', trueDamage:true, ignoreCover:true, ignoreToughBody:true});
      u.dmgDone += lethal;
      executeCount++;
      secondHits++;
    } else {
      const dmg = calcOutgoingDamage(u,20,target,'执行……·第二枪');
      damageUnit(target.id, dmg, 0, `${u.name} 执行……·第二枪 命中 ${target.name}`, u.id,{skillFx:'neyla:执行……'});
      u.dmgDone += dmg;
      secondHits++;
    }
  }
  if(secondHits>0){
    appendLog(`执行……·第二枪 命中 ${secondHits} 人${executeCount>0 ? `，处决 ${executeCount}` : ''}`);
  } else {
    appendLog('执行……·第二枪 未命中任何目标');
  }
  applySelfCost(15, 40, '第二枪');
  unitActed(u);
}

// —— Kyn —— 
function kynReturnToHaz(u){
  const haz = units['haz'];
  if(!haz || haz.hp<=0){ appendLog('迅影返身：Haz 已不在场，无法回归'); return; }
  const adj = range_adjacent(haz).filter(p=>!getUnitAt(p.r,p.c));
  if(adj.length===0){ appendLog('迅影返身：Haz 身旁无空位'); return; }
  let best=adj[0], bestD=mdist(u,adj[0]);
  for(const p of adj){ const d=mdist(u,p); if(d<bestD){ best=p; bestD=d; } }
  u.r = best.r; u.c = best.c; pulseCell(u.r,u.c);
  appendLog(`${u.name} 迅影返身：回归队长身侧`);
}
async function kyn_ShadowDash(u, target){
  if(!target || target.side===u.side){ appendLog('迅影突刺 目标无效'); return; }
  await telegraphThenImpact([{r:target.r,c:target.c}]);
  const adj = range_adjacent(target).filter(p=>!getUnitAt(p.r,p.c));
  if(adj.length){ const p=adj[0]; u.r=p.r; u.c=p.c; pulseCell(u.r,u.c); }
  const thresh = Math.ceil(target.maxHp*0.25);
  let executed = false;

  if(target.hp<=thresh){
    damageUnit(target.id, target.hp, 0, `${u.name} 迅影突刺 处决 ${target.name}`, u.id,{skillFx:'kyn:迅影突刺'});
    executed = true;
  } else {
    const before = target.hp;
    damageUnit(target.id, 20, 0, `${u.name} 迅影突刺 命中 ${target.name}`, u.id,{skillFx:'kyn:迅影突刺'});
    if(before>0 && target.hp<=0) executed = true;
  }
  if(u.passives.includes('kynReturn') && executed){
    kynReturnToHaz(u);
  }
  unitActed(u);
}
async function kyn_DeathCall(u, target){
  if(!target || target.side===u.side){ appendLog('死亡宣告 目标无效'); return; }
  await telegraphThenImpact([{r:target.r,c:target.c}]);
  const thresh = Math.ceil(target.maxHp*0.30);
  let executed = false;

  if(target.hp<=thresh){
    damageUnit(target.id, target.hp, 0, `${u.name} 死亡宣告 处决 ${target.name}`, u.id,{skillFx:'kyn:死亡宣告'});
    executed = true;
  } else {
    const before = target.hp;
    damageUnit(target.id, 50, 30, `${u.name} 死亡宣告 重创 ${target.name}`, u.id,{skillFx:'kyn:死亡宣告'});
    if(before>0 && target.hp<=0) executed = true;
  }
  if(u.passives.includes('kynReturn') && executed){
    kynReturnToHaz(u);
  }
  unitActed(u);
}
// Kyn：割喉飞刃（4格内单体 20HP + 流血1 + 恐惧1）
async function kyn_ThroatBlade(u, aim){
  const tu = getUnitAt(aim.r, aim.c);
  if(!tu || tu.side==='enemy'){ appendLog('割喉飞刃 未命中'); unitActed(u); return; }
  if(mdist(u,tu) > 4){ appendLog('割喉飞刃 超出射程（≤4）'); unitActed(u); return; }
  await telegraphThenImpact([{r:tu.r,c:tu.c}]);
  const dmg = calcOutgoingDamage(u,20,tu,'割喉飞刃');
  cameraFocusOnCell(tu.r, tu.c);
  damageUnit(tu.id, dmg, 0, `${u.name} 割喉飞刃 命中 ${tu.name}`, u.id,{skillFx:'kyn:割喉飞刃'});
  addStatusStacks(tu,'bleed',1,{label:'流血', type:'debuff'});
  addStatusStacks(tu,'paralyzed',1,{label:'恐惧', type:'debuff'});
  appendLog(`${tu.name} 附加 流血+1、恐惧+1`);
  unitActed(u);
}
// Kyn：影杀之舞（2步 常态 3x3 AOE 30，随后免费移动1格；不受掩体）
async function kyn_ShadowDance_AOE(u){
  const cells = range_square_n(u,1);
  await telegraphThenImpact(cells);
  const seen=new Set(); let hits=0;
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      damageUnit(tu.id, 30, 0, `${u.name} 影杀之舞 横扫 ${tu.name}`, u.id, {ignoreCover:true, skillFx:'kyn:影杀之舞'});
      seen.add(tu.id); hits++;
    }
  }
  appendLog(`影杀之舞 AOE 命中 ${hits} 人`);
  // 立即免费移动1格（若有空位）
  const neigh = range_adjacent(u).filter(p=>!getUnitAt(p.r,p.c));
  if(neigh.length){
    const p = neigh[0];
    showTrail(u.r,u.c,p.r,p.c);
    u.r=p.r; u.c=p.c; pulseCell(u.r,u.c);
    appendLog(`${u.name} 影杀之舞：免费位移 1 格`);
  }
  unitActed(u);
}

// —— Lirathe Skills（Phase 1 & Phase 2） ——
async function lirathe_DashSlash(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  setUnitFacing(u, dir);
  const cells = range_forward_n(u,4,dir);
  await telegraphThenImpact(cells);
  
  let finalTarget = null;
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy') finalTarget = tu;
  }
  
  // Dash to the cell (stop at last enemy or at end)
  let newR=u.r, newC=u.c;
  for(const c of cells){
    const occ=getUnitAt(c.r,c.c);
    if(occ && occ.side!=='enemy') break;
    if(!occ || occ===u){ newR=c.r; newC=c.c; }
  }
  if(newR!==u.r || newC!==u.c){
    showTrail(u.r,u.c,newR,newC);
    u.r=newR; u.c=newC;
  }
  
  if(finalTarget){
    damageUnit(finalTarget.id, 15, 0, `${u.name} 刺斩 ${finalTarget.name}`, u.id, {skillName:'刺斩'});
    // Add 脆弱 debuff (15% more damage this turn)
    if(!finalTarget.status.vulnerableStacks) finalTarget.status.vulnerableStacks = 0;
    finalTarget.status.vulnerableStacks += 1;
    updateStatusStacks(finalTarget,'vulnerableStacks',finalTarget.status.vulnerableStacks,{label:'脆弱',type:'debuff'});
    appendLog(`${finalTarget.name} 受到脆弱Debuff（本回合伤害+15%）`);
  } else {
    appendLog(`${u.name} 刺斩 未命中`);
  }
  renderAll();
  unitActed(u);
}

async function lirathe_EscapeMove(u, payload){
  const {r,c,dir} = payload;
  if(!r || !c) return unitActed(u);
  const prevR=u.r, prevC=u.c;
  u.r=r; u.c=c;
  if(dir) setUnitFacing(u, dir);
  showTrail(prevR,prevC,r,c);
  appendLog(`${u.name} 又想逃？ 移动至 (${r},${c})`);
  
  // Check adjacent enemies and deal 5HP
  const adj = range_adjacent(u);
  for(const p of adj){
    const tu=getUnitAt(p.r,p.c);
    if(tu && tu.side!=='enemy'){
      damageUnit(tu.id, 5, 0, `${u.name} 又想逃 擦过 ${tu.name}`, u.id, {skillName:'又想逃'});
    }
  }
  renderAll();
  unitActed(u);
}

async function lirathe_BladeAbsorb(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  setUnitFacing(u, dir);
  const cells = forwardRectCentered(u,dir,3,2);
  await telegraphThenImpact(cells);
  
  const seen=new Set();
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      damageUnit(tu.id, 20, 0, `${u.name} 刀光吸入 ${tu.name}`, u.id, {skillName:'刀光吸入'});
      // Add blade light stack
      if(!tu.status.bladeLightStacks) tu.status.bladeLightStacks = 0;
      tu.status.bladeLightStacks += 1;
      updateStatusStacks(tu,'bladeLightStacks',tu.status.bladeLightStacks,{label:'刀光',type:'debuff'});
      
      // Check if blade light reaches 10 stacks
      if(tu.status.bladeLightStacks >= 10){
        const burstDmg = tu.status.bladeLightStacks * 5;
        damageUnit(tu.id, burstDmg, burstDmg, `刀光爆炸 ${tu.name}`, u.id, {skillName:'刀光爆炸'});
        u.hp = Math.min(u.maxHp, u.hp + burstDmg);
        u.sp = Math.min(u.maxSp, u.sp + burstDmg);
        showDamageFloat(u, -burstDmg, -burstDmg);
        appendLog(`${u.name} 刀光爆炸：恢复 ${burstDmg} HP/SP`);
        tu.status.bladeLightStacks = 0;
        updateStatusStacks(tu,'bladeLightStacks',0,{label:'刀光',type:'debuff'});
      }
      seen.add(tu.id);
    }
  }
  renderAll();
  unitActed(u);
}

async function lirathe_SwordDance(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  setUnitFacing(u, dir);
  
  let hitCount = 0;
  const seen=new Set();
  
  // Stage 1: Forward 3x2
  let cells = forwardRectCentered(u,dir,3,2);
  await telegraphThenImpact(cells);
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      damageUnit(tu.id, 20, 0, `${u.name} 剑舞阶段1 ${tu.name}`, u.id, {skillName:'剑舞'});
      if(!tu.status.vulnerableStacks) tu.status.vulnerableStacks = 0;
      tu.status.vulnerableStacks += 1;
      updateStatusStacks(tu,'vulnerableStacks',tu.status.vulnerableStacks,{label:'脆弱',type:'debuff'});
      hitCount++; seen.add(tu.id);
    }
  }
  
  // Stage 2: Reverse direction
  const revDir = {up:'down',down:'up',left:'right',right:'left'}[dir] || dir;
  cells = forwardRectCentered(u,revDir,3,2);
  await telegraphThenImpact(cells);
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      damageUnit(tu.id, 20, 0, `${u.name} 剑舞阶段2 ${tu.name}`, u.id, {skillName:'剑舞'});
      hitCount++; seen.add(tu.id);
    }
  }
  
  // Stage 3: 3x3
  cells = range_square_n(u,1);
  await telegraphThenImpact(cells);
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      damageUnit(tu.id, 10, 0, `${u.name} 剑舞阶段3 ${tu.name}`, u.id, {skillName:'剑舞'});
      hitCount++; seen.add(tu.id);
    }
  }
  
  // Stage 4: 5x5
  cells = range_square_n(u,2);
  await telegraphThenImpact(cells);
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      damageUnit(tu.id, 15, 0, `${u.name} 剑舞阶段4 ${tu.name}`, u.id, {skillName:'剑舞'});
      if(!tu.status.bladeLightStacks) tu.status.bladeLightStacks = 0;
      tu.status.bladeLightStacks += 1;
      updateStatusStacks(tu,'bladeLightStacks',tu.status.bladeLightStacks,{label:'刀光',type:'debuff'});
      hitCount++; seen.add(tu.id);
    }
  }
  
  // Stage 5: 7x7
  cells = range_square_n(u,3);
  await telegraphThenImpact(cells);
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      damageUnit(tu.id, 15, 0, `${u.name} 剑舞阶段5 ${tu.name}`, u.id, {skillName:'剑舞'});
      if(!tu.status.bladeLightStacks) tu.status.bladeLightStacks = 0;
      tu.status.bladeLightStacks += 1;
      updateStatusStacks(tu,'bladeLightStacks',tu.status.bladeLightStacks,{label:'刀光',type:'debuff'});
      hitCount++; seen.add(tu.id);
    }
  }
  
  // If all stages hit at least one enemy, add mockery buff
  if(hitCount >= 5){
    if(!u.status.mockeryStacks) u.status.mockeryStacks = 0;
    u.status.mockeryStacks += 1;
    updateStatusStacks(u,'mockeryStacks',u.status.mockeryStacks,{label:'戏谑',type:'buff'});
    appendLog(`${u.name} 剑舞全段命中：获得戏谑Buff`);
  }
  
  renderAll();
  unitActed(u);
}

async function lirathe_SplashBlade(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  setUnitFacing(u, dir);
  const line = range_line(u,dir);
  
  // Stage 1: Hit first enemy
  await telegraphThenImpact(line);
  let firstTarget = null;
  for(const c of line){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy'){ firstTarget = tu; break; }
  }
  if(firstTarget){
    damageUnit(firstTarget.id, 15, 0, `${u.name} 飞溅刀光阶段1 ${firstTarget.name}`, u.id, {skillName:'飞溅刀光'});
    if(!firstTarget.status.bladeLightStacks) firstTarget.status.bladeLightStacks = 0;
    firstTarget.status.bladeLightStacks += 1;
    updateStatusStacks(firstTarget,'bladeLightStacks',firstTarget.status.bladeLightStacks,{label:'刀光',type:'debuff'});
  }
  
  // Stage 2: Hit all enemies in line
  await telegraphThenImpact(line);
  const seen=new Set();
  for(const c of line){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      damageUnit(tu.id, 15, 0, `${u.name} 飞溅刀光阶段2 ${tu.name}`, u.id, {skillName:'飞溅刀光'});
      if(!tu.status.bladeLightStacks) tu.status.bladeLightStacks = 0;
      tu.status.bladeLightStacks += 1;
      updateStatusStacks(tu,'bladeLightStacks',tu.status.bladeLightStacks,{label:'刀光',type:'debuff'});
      seen.add(tu.id);
    }
  }
  
  // Stage 3: Charge and pierce first target
  if(firstTarget && firstTarget.hp>0){
    await telegraphThenImpact([{r:firstTarget.r,c:firstTarget.c}]);
    damageUnit(firstTarget.id, 5, 0, `${u.name} 飞溅刀光阶段3贯穿 ${firstTarget.name}`, u.id, {skillName:'飞溅刀光'});
    if(!firstTarget.status.bladeLightStacks) firstTarget.status.bladeLightStacks = 0;
    firstTarget.status.bladeLightStacks += 1;
    updateStatusStacks(firstTarget,'bladeLightStacks',firstTarget.status.bladeLightStacks,{label:'刀光',type:'debuff'});
  }
  
  renderAll();
  unitActed(u);
}

async function lirathe_DontRun(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  setUnitFacing(u, dir);
  const line = range_line(u,dir);
  await telegraphThenImpact(line);
  
  let firstTarget = null;
  for(const c of line){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy'){ firstTarget = tu; break; }
  }
  
  if(firstTarget){
    damageUnit(firstTarget.id, 0, 15, `${u.name} 别跑蛛网 ${firstTarget.name}`, u.id, {skillName:'别跑'});
    // 50% chance to immobilize
    if(Math.random() < 0.5){
      if(!firstTarget.status.immobilizedTurns) firstTarget.status.immobilizedTurns = 0;
      firstTarget.status.immobilizedTurns += 1;
      updateStatusStacks(firstTarget,'immobilizedTurns',firstTarget.status.immobilizedTurns,{label:'禁锢',type:'debuff'});
      appendLog(`${firstTarget.name} 被禁锢（下回合无法移动）`);
    }
  } else {
    appendLog(`${u.name} 别跑 未命中`);
  }
  
  renderAll();
  unitActed(u);
}

// Phase 2 skills
async function lirathe_ChargeKill(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  setUnitFacing(u, dir);
  const line = range_line(u,dir);
  await telegraphThenImpact(line);
  
  const seen=new Set();
  let newR=u.r, newC=u.c;
  
  for(const c of line){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy'){
      damageUnit(tu.id, 20, 10, `${u.name} 冲杀 ${tu.name}`, u.id, {skillName:'冲杀'});
      // Add corrosion
      if(!tu.status.corrosionStacks) tu.status.corrosionStacks = 0;
      tu.status.corrosionStacks += 1;
      updateStatusStacks(tu,'corrosionStacks',tu.status.corrosionStacks,{label:'腐蚀',type:'debuff'});
      seen.add(tu.id);
    }
    if(!tu || tu===u){ newR=c.r; newC=c.c; }
  }
  
  if(newR!==u.r || newC!==u.c){
    showTrail(u.r,u.c,newR,newC);
    u.r=newR; u.c=newC;
  }
  
  renderAll();
  unitActed(u);
}

async function lirathe_WhereAreYou(u){
  const cells = range_square_n(u,3);
  await telegraphThenImpact(cells);
  
  const seen=new Set();
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
      damageUnit(tu.id, 0, 10, `${u.name} 你在哪吼叫 ${tu.name}`, u.id, {skillName:'你在哪'});
      // Add corrosion
      if(!tu.status.corrosionStacks) tu.status.corrosionStacks = 0;
      tu.status.corrosionStacks += 1;
      updateStatusStacks(tu,'corrosionStacks',tu.status.corrosionStacks,{label:'腐蚀',type:'debuff'});
      // Add "seen" buff for Lirathe to see the unit
      if(!tu.status.seenTurns) tu.status.seenTurns = 0;
      tu.status.seenTurns = 1;
      updateStatusStacks(tu,'seenTurns',tu.status.seenTurns,{label:'看见',type:'debuff'});
      seen.add(tu.id);
    }
  }
  
  renderAll();
  unitActed(u);
}

async function lirathe_RipHeart(u, desc){
  // Find target in 2x2 area in front
  const dir = desc && desc.dir ? desc.dir : u.facing;
  setUnitFacing(u, dir);
  
  let target = null;
  for(let dr=0;dr<=1;dr++){
    for(let dc=0;dc<=1;dc++){
      const rr=u.r+DIRS[dir].dr+dr, cc=u.c+DIRS[dir].dc+dc;
      const tu=getUnitAt(rr,cc);
      if(tu && tu.side!=='enemy'){ target = tu; break; }
    }
    if(target) break;
  }
  
  if(!target){
    appendLog(`${u.name} 掏心掏肺 未找到目标`);
    return unitActed(u);
  }
  
  const cells = [{r:target.r,c:target.c}];
  
  // 3 tears
  for(let i=0;i<3;i++){
    await telegraphThenImpact(cells);
    if(target.hp>0){
      damageUnit(target.id, 15, 5, `${u.name} 掏心掏肺撕扯${i+1} ${target.name}`, u.id, {skillName:'掏心掏肺'});
      if(!target.status.corrosionStacks) target.status.corrosionStacks = 0;
      target.status.corrosionStacks += 1;
      updateStatusStacks(target,'corrosionStacks',target.status.corrosionStacks,{label:'腐蚀',type:'debuff'});
    }
  }
  
  // If corrosion > 5, repeat
  if(target.hp>0 && target.status.corrosionStacks > 5){
    appendLog(`${target.name} 腐蚀层数>5，重复掏心掏肺！`);
    for(let i=0;i<3;i++){
      await telegraphThenImpact(cells);
      if(target.hp>0){
        damageUnit(target.id, 15, 5, `${u.name} 掏心掏肺重复${i+1} ${target.name}`, u.id, {skillName:'掏心掏肺'});
        if(!target.status.corrosionStacks) target.status.corrosionStacks = 0;
        target.status.corrosionStacks += 1;
        updateStatusStacks(target,'corrosionStacks',target.status.corrosionStacks,{label:'腐蚀',type:'debuff'});
      }
    }
  }
  
  renderAll();
  unitActed(u);
}

async function lirathe_CantFindWay(u){
  // Charge in 4 directions
  for(const dir of ['up','down','left','right']){
    setUnitFacing(u, dir);
    const line = range_line(u,dir);
    await telegraphThenImpact(line);
    
    const seen=new Set();
    for(const c of line){
      const tu=getUnitAt(c.r,c.c);
      if(tu && tu.side!=='enemy' && !seen.has(tu.id)){
        damageUnit(tu.id, 20, 10, `${u.name} 找不到路${dir} ${tu.name}`, u.id, {skillName:'找不到路'});
        if(!tu.status.corrosionStacks) tu.status.corrosionStacks = 0;
        tu.status.corrosionStacks += 1;
        updateStatusStacks(tu,'corrosionStacks',tu.status.corrosionStacks,{label:'腐蚀',type:'debuff'});
        seen.add(tu.id);
      }
    }
  }
  
  renderAll();
  unitActed(u);
}

// Consciousness Flower skill
async function consciousFlower_Resist(u, desc){
  const dir = desc && desc.dir ? desc.dir : u.facing;
  setUnitFacing(u, dir);
  const cells = range_forward_n(u,3,dir);
  await telegraphThenImpact(cells);
  
  let target = null;
  for(const c of cells){
    const tu=getUnitAt(c.r,c.c);
    if(tu && tu.side!=='enemy'){ target = tu; break; }
  }
  
  if(target){
    damageUnit(target.id, 15, 5, `${u.name} 抵抗 ${target.name}`, u.id, {skillName:'抵抗'});
  } else {
    appendLog(`${u.name} 抵抗 未命中`);
  }
  
  renderAll();
  unitActed(u);
}


// —— Neyla 压迫后“终末之影”保证（每回合最多一张；无则添加/替换） ——
function makeNeylaEndShadowSkill(u){
  return skill('终末之影',2,'red','全图任意单体 50HP+20SP',
    (uu)=> inRadiusCells(uu,999,{allowOccupied:true}).map(p=>({...p,dir:uu.facing})),
    (uu,aim)=> neyla_EndShadow(uu,aim),
    {aoe:false},
    {cellTargeting:true, castMs:1200}
  );
}
function ensureNeylaEndShadowGuarantee(u){
  if(!u || u.id!=='neyla' || !u.oppression) return;
  const pool = u.skillPool || [];
  const firstIdx = pool.findIndex(s=>s && s.name==='终末之影');
  for(let i=pool.length-1;i>=0;i--){
    if(i!==firstIdx && pool[i] && pool[i].name==='终末之影'){
      pool.splice(i,1);
    }
  }
  if(firstIdx>=0) return;
  const endShadow = makeNeylaEndShadowSkill(u);
  if(pool.length < SKILLPOOL_MAX){
    pool.push(endShadow);
  } else {
    const idx = Math.floor(Math.random()*pool.length);
    pool[idx] = endShadow;
  }
  appendLog('Neyla 压迫：已保证“终末之影”在手牌中（最多仅一张）');
}

// —— 技能池/抽牌（含调整：Katz/Nelya/Kyn 技能）；移动卡统一蓝色 —— 
function skill(name,cost,color,desc,rangeFn,execFn,estimate={},meta={}){ return {name,cost,color,desc,rangeFn,execFn,estimate,meta}; }

// Helper function to load selected skills from localStorage
function loadSelectedSkillsForBattle() {
  try {
    const saved = localStorage.getItem('gwdemo_selected_skills');
    return saved ? JSON.parse(saved) : null;
  } catch (e) {
    return null;
  }
}

// Helper function to check if skill selection should be applied (level 50+)
function shouldApplySkillSelection(u) {
  return u && u.level >= 50;
}

// Skill key mapping from skill library to battle script
const skillKeyMapping = {
  adora: {
    'adora_dagger': '短匕轻挥',
    'adora_gun': '枪击',
    'adora_dont_approach': '呀！你不要靠近我呀！！',
    'adora_stun_device': '自制粉色迷你电击装置',
    'adora_medical': '略懂的医术！',
    'adora_cheer': '加油哇！',
    'adora_rely': '只能靠你了。。',
    'adora_bloom': '绽放（红色）',
    'adora_assassination_1': '课本知识：刺杀一'
  },
  karma: {
    'karma_punch': '沙包大的拳头',
    'karma_gun': '枪击',
    'karma_listen': '都听你的',
    'karma_blood_grip': '嗜血之握',
    'karma_deep_breath': '深呼吸',
    'karma_adrenaline': '肾上腺素'
  },
  dario: {
    'dario_claw': '机械爪击',
    'dario_gun': '枪击',
    'dario_swift': '迅捷步伐',
    'dario_pull': '拿来吧你！',
    'dario_bitter_sweet': '先苦后甜',
    'dario_tear_wound': '撕裂伤口',
    'dario_status_recovery': '状态恢复'
  }
};

// Helper function to get selected skill keys for filtering
function getSelectedSkillKeysForUnit(u) {
  if (!shouldApplySkillSelection(u)) return null;
  
  const selectedSkills = loadSelectedSkillsForBattle();
  if (!selectedSkills || !selectedSkills[u.id]) return null;
  
  const charSelection = selectedSkills[u.id];
  const mapping = skillKeyMapping[u.id];
  if (!mapping) return null;
  
  const selectedKeys = new Set();
  
  // Add skills from each color slot
  for (const color of ['green', 'blue', 'pink', 'white', 'red']) {
    if (charSelection[color]) {
      const battleKey = mapping[charSelection[color]];
      if (battleKey) selectedKeys.add(battleKey);
    }
  }
  
  // Add orange skills (can have multiple)
  if (Array.isArray(charSelection.orange)) {
    for (const skillId of charSelection.orange) {
      const battleKey = mapping[skillId];
      if (battleKey) selectedKeys.add(battleKey);
    }
  }
  
  return selectedKeys.size > 0 ? selectedKeys : null;
}

function buildSkillFactoriesForUnit(u){
  const F=[];
  if(u.id==='adora' || u.id==='adora_phantom'){
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
      { key:'加油哇！', prob:0.20, cond:()=>u.level>=25, make:()=> skill('加油哇！',2,'orange','以自身为中心5x5内选择友方：赋予 1 层“鸡血”（下一次攻击伤害翻倍，使用后移除）',
        (uu)=> range_square_n(uu,2).filter(p=>{ const tu=getUnitAt(p.r,p.c); return tu && tu.side===uu.side; }),
        (uu,aim)=> adoraCheer(uu,aim),
        {aoe:false},
        {cellTargeting:true, castMs:900}
      )},
      { key:'只能靠你了。。', prob:0.15, cond:()=>u.level>=35, make:()=> skill('只能靠你了。。',4,'orange','牺牲25HP；以自身为中心5格范围友方，赋予1层“依赖”（下一次攻击造成真实伤害（无视所有防御或者免伤）以及叠两层眩晕层数，并消耗一层依赖以及将此单位的SP降为0，（每单位最多一层依赖））',
        (uu)=> range_square_n(uu,5).filter(p=>{ const tu=getUnitAt(p.r,p.c); return tu && tu.side===uu.side; }),
        (uu,aim)=> adoraDepend(uu,aim),
        {aoe:false},
        {cellTargeting:true, castMs:900}
      )}
    );
    F.push(
      { key:'课本知识：刺杀一', prob:0.80, cond:()=>u.level>=50, make:()=> skill('课本知识：刺杀一',1,'green','四周2格瞬移到敌人后侧，插入10HP+5SP，拔出5HP+5SP+1层流血',
        (uu,aimDir,aimCell)=> aimCell && mdist(uu,aimCell)<=2? [{r:aimCell.r,c:aimCell.c,dir:cardinalDirFromDelta(aimCell.r-uu.r,aimCell.c-uu.c)}] : range_move_radius(uu,2).filter(p=>{ const tu=getUnitAt(p.r,p.c); return tu && tu.side!==uu.side; }),
        (uu,target)=> adoraAssassination(uu,target),
        {},
        {castMs:1200}
      )},
    );
    F.push(
      { key:'绽放（红色）', prob:0.20, cond:()=>u.level>=50 && !(u.skillPool||[]).some(s=>s.name==='绽放（红色）'), make:()=> skill('绽放（红色）',3,'red','被动：在技能池时，队友攻击敌人叠加血色花蕾（每个敌人最多7层）；主动：引爆所有血色花蕾，造成真实伤害（每层 10HP+5SP），并让 Adora 自身恢复（每层 +5HP/+5SP）同时治疗 5 格内友方（含自身，每层 +3HP/+3SP）',
        (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
        (uu)=> adoraBloom(uu),
        {},
        {castMs:1200}
      )}
    );
  } else if(u.id==='dario' || u.id==='dario_phantom'){
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
    F.push(
      { key:'撕裂伤口', prob:0.80, cond:()=>u.level>=50, make:()=> skill('撕裂伤口',1,'green','前3格爪击15HP叠1流血（非满血伤害+50%再叠1流血），抽出利爪5HP',
        (uu,aimDir)=> aimDir? range_forward_n(uu,3,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,3,d).forEach(x=>a.push(x)); return a;})(),
        (uu,targetOrDesc)=> {
          if(targetOrDesc && targetOrDesc.id) darioTearWound(uu,targetOrDesc);
          else if(targetOrDesc && targetOrDesc.dir){
            const line = range_forward_n(uu,3,targetOrDesc.dir);
            let tgt=null; for(const c of line){ const tu=getUnitAt(c.r,c.c); if(tu && tu.side!=='player'){ tgt=tu; break; } }
            if(tgt) darioTearWound(uu,tgt); else appendLog('撕裂伤口 未命中');
          }
        },
        {},
        {castMs:1100}
      )},
      { key:'状态恢复', prob:0.15, cond:()=>u.level>=50, make:()=> skill('状态恢复',2,'orange','选中全图友方单位，移除所有负面效果，增加15SP',
        (uu)=> inRadiusCells(uu,999,{allowOccupied:true}).filter(p=>{ const tu=getUnitAt(p.r,p.c); return tu && tu.side===uu.side; }),
        (uu,aim)=> darioStatusRecovery(uu,aim),
        {aoe:false},
        {cellTargeting:true, castMs:900}
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
    F.push(
      { key:'肾上腺素', prob:0.20, cond:()=>u.level>=50 && !(u.skillPool||[]).some(s=>s.name==='肾上腺素'), make:()=> skill('肾上腺素',2,'white','主动：给自己上1层鸡血并恢复15HP和5SP。被动：每连续2次"沙包大的拳头"命中后自动再使用两次（技能池最多1张）',
        (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
        (uu)=> karmaAdrenaline(uu),
        {},
        {castMs:700}
      )}
    );
  } else if(u.id==='haz'){
    if(!u._comeback){
      F.push(
        { key:'鱼叉穿刺', prob:0.70, cond:()=>true, make:()=> skill('鱼叉穿刺',1,'green','前方1格 20伤害 自身+10SP',
          (uu,aimDir)=> aimDir? range_forward_n(uu,1,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,1,d).forEach(x=>a.push(x)); return a;})(),
          (uu,descOrTarget)=> {
            let tgt=null, dir=uu.facing;
            if(descOrTarget && descOrTarget.id) tgt=descOrTarget;
            else if(descOrTarget && descOrTarget.dir){ dir=descOrTarget.dir; const cell=forwardCellAt(uu,dir,1); if(cell) tgt=getUnitAt(cell.r,cell.c); }
            if(tgt) haz_HarpoonStab(uu,tgt); else appendLog('鱼叉穿刺 未命中');
          },
          {},
          {castMs:1100}
        )},
        { key:'深海猎杀', prob:0.60, cond:()=>true, make:()=> skill('深海猎杀',2,'red','前方3格内命中 25伤害 拉到面前 SP-10',
          (uu,aimDir)=> aimDir? range_forward_n(uu,3,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,3,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> haz_DeepHunt(uu,desc),
          {},
          {castMs:1200}
        )},
        { key:'猎神之叉', prob:0.65, cond:()=>true, make:()=> skill('猎神之叉',2,'red','5x5内选择敌人：瞬移至其身旁并造成20(50%概率x2)+15SP并施加流血(2)',
          (uu)=> range_square_n(uu,2),
          (uu,aim)=> { const tu = aim && aim.id ? aim : getUnitAt(aim.r, aim.c); if(tu && tu.side!=='enemy') haz_GodFork(uu,tu); else appendLog('猎神之叉 未命中'); },
          {},
          {cellTargeting:true, castMs:1200}
        )},
        { key:'锁链缠绕', prob:0.50, cond:()=>true, make:()=> skill('锁链缠绕',2,'green','2回合内伤害-40%，下次被打反击10SP，队伍+5SP',
          (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
          (uu)=> haz_ChainShield(uu),
          {},
          {castMs:600}
        )},
        { key:'鲸落', prob:0.30, cond:()=>true, make:()=> skill('鲸落',4,'red','自身中心5x5 50HP +20SP，并使目标下回合-1步（AOE不受掩体）',
          (uu)=> range_square_n(uu,2),
          (uu)=> haz_WhaleFall(uu),
          {aoe:true},
          {castMs:1300}
        )}
      );
    } else {
      F.push(
        { key:'深海猎杀', prob:0.70, cond:()=>true, make:()=> skill('深海猎杀',2,'red','前方3格内命中 25伤害 拉到面前 SP-10（力挽狂澜）',
          (uu,aimDir)=> aimDir? range_forward_n(uu,3,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,3,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> haz_DeepHunt(uu,desc),
          {},
          {castMs:1200}
        )},
        { key:'怨念滋生', prob:0.33, cond:()=>true, make:()=> skill('怨念滋生',1,'green','全图：对被猎杀标记目标 施加1流血+1恐惧',
          (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
        (uu)=> { if(!hazMarkedTargetId){ appendLog('怨念滋生：没有被标记的目标'); unitActed(uu); return; } const t=units[hazMarkedTargetId]; if(!t||t.hp<=0){ appendLog('怨念滋生：标记目标不存在或已倒下'); unitActed(uu); return; } addTempClassToCells([{r:t.r,c:t.c}],'highlight-tele',TELEGRAPH_MS); setTimeout(()=>{ addStatusStacks(t,'bleed',1,{label:'流血', type:'debuff'}); addStatusStacks(t,'paralyzed',1,{label:'恐惧', type:'debuff'}); showSkillFx('haz:怨念滋生',{target:t}); appendLog(`${uu.name} 怨念滋生：对 ${t.name} 施加 1层流血 与 1层恐惧`); }, TELEGRAPH_MS); unitActed(uu); },
          {},
          {castMs:800}
        )},
        { key:'付出代价', prob:0.33, cond:()=>true, make:()=> skill('付出代价',2,'red','前刺3/穿刺4/横斩(横3x前2)，逐段即时结算',
          (uu,aimDir)=> aimDir? range_forward_n(uu,4,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,4,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> haz_PayThePrice(uu,desc),
          {aoe:true},
          {castMs:2000}
        )},
        { key:'仇恨之叉', prob:0.33, cond:()=>true, make:()=> skill('仇恨之叉',2,'red','横斩(横3x前2)+自身5x5重砸，逐段即时结算',
          (uu,aimDir)=> aimDir? forwardRectCentered(uu,aimDir,3,2) : (()=>{const a=[]; for(const d in DIRS) forwardRectCentered(uu,d,3,2).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> haz_ForkOfHatred(uu,desc),
          {aoe:true},
          {castMs:1900}
        )}
      );
    }
  } else if(u.id==='katz'){
    if(!u.oppression){
      F.push(
        { key:'矛刺', prob:0.60, cond:()=>true, make:()=> skill('矛刺',1,'green','前方1格 20伤 自身+5SP',
          (uu,aimDir)=> aimDir? range_forward_n(uu,1,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,1,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=>{ let tgt=null, dir=uu.facing; if(desc && desc.dir){ dir=desc.dir; const c=forwardCellAt(uu,dir,1); if(c) tgt=getUnitAt(c.r,c.c); } if(tgt) katz_Thrust(uu,tgt); else appendLog('矛刺 未命中'); },
          {},
          {castMs:1000}
        )},
        { key:'链式鞭击', prob:0.50, cond:()=>true, make:()=> skill('链式鞭击',2,'red','前方3格逐格 25伤 使下回合-1步',
          (uu,aimDir)=> aimDir? range_forward_n(uu,3,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,3,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> katz_ChainWhip(uu,desc),
          {},
          {castMs:1200}
        )},
        { key:'反复鞭尸', prob:0.50, cond:()=>true, make:()=> skill('反复鞭尸',3,'red','前方3格AOE：每轮10/15HP并+5SP，按SP百分比重复（最多5次）',
          (uu,aimDir)=> aimDir? range_forward_n(uu,3,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,3,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> katz_RepeatedWhip(uu,desc),
          {},
          {castMs:1400}
        )},
        { key:'终焉礼炮', prob:0.35, cond:()=>true, make:()=> skill('终焉礼炮',3,'red','直线5格 35HP（不受掩体）',
          (uu,aimDir)=> aimDir? range_forward_n(uu,5,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,5,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> katz_EndSalvo(uu,desc),
          {aoe:true},
          {castMs:1400}
        )}
      );
    } else {
      F.push(
        { key:'必须抹杀一切。。', prob:0.55, cond:()=>true, make:()=> skill('必须抹杀一切。。',2,'red','前方3格多段：20/30伤（自损5HP/段），每段+5SP（最多5段）',
          (uu,aimDir)=> aimDir? range_forward_n(uu,3,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,3,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> katz_MustErase(uu,desc),
          {aoe:true},
          {castMs:1800}
        )},
        { key:'终焉礼炮', prob:0.45, cond:()=>true, make:()=> skill('终焉礼炮',3,'red','直线5格 35HP（不受掩体）',
          (uu,aimDir)=> aimDir? range_forward_n(uu,5,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,5,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> katz_EndSalvo(uu,desc),
          {aoe:true},
          {castMs:1400}
        )}
      );
    }
  } else if(u.id==='tusk'){
    if(!u.oppression){
      F.push(
        { key:'骨盾猛击', prob:0.70, cond:()=>true, make:()=> skill('骨盾猛击',1,'green','邻格 10伤 击退1格',
          (uu,aimDir,aimCell)=> aimCell && mdist(uu,aimCell)===1? [{r:aimCell.r,c:aimCell.c,dir:cardinalDirFromDelta(aimCell.r-uu.r,aimCell.c-uu.c)}] : range_adjacent(uu),
          (uu,target)=> tusk_ShieldBash(uu,target),
          {},
          {castMs:1000}
        )},
        { key:'来自深海的咆哮', prob:0.50, cond:()=>true, make:()=> skill('来自深海的咆哮',2,'red','3x3范围 敌方SP -20',
          (uu)=> range_square_n(uu,1),
          (uu)=> tusk_DeepRoar(uu),
          {aoe:true},
          {castMs:1200}
        )},
        { key:'战争堡垒', prob:0.45, cond:()=>true, make:()=> skill('战争堡垒',2,'red','进入防御姿态：3回合内伤害-50%且每回合+10SP（期间无法移动）',
          (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
          (uu)=> tusk_WarFortress(uu),
          {},
          {castMs:700}
        )},
        { key:'牛鲨冲撞', prob:0.45, cond:()=>true, make:()=> skill('牛鲨冲撞',2,'blue','向一方向冲锋≤3格，撞击第一个敌人造成20伤并击退1格；否则移动到终点',
          (uu,aimDir)=> aimDir? range_forward_n(uu,3,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,3,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> tusk_BullCharge(uu,desc),
          {},
          {moveSkill:true, moveRadius:3, castMs:900}
        )}
      );
    } else {
      F.push(
        { key:'拼尽全力保卫队长', prob:0.60, cond:()=>true, make:()=> skill('拼尽全力保卫队长',2,'red','进入反伤姿态：3回合内伤害-40%、每回合+10SP、反弹30%所受HP伤（期间无法移动）',
          (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
          (uu)=> tusk_RetaliateGuard(uu),
          {},
          {castMs:700}
        )}
      );
    }
  } else if(u.id==='neyla'){
    if(!u.oppression){
      F.push(
        { key:'迅捷射击', prob:0.70, cond:()=>true, make:()=> skill('迅捷射击',1,'green','4格内单体 15HP +5SP',
          (uu,aimDir,aimCell)=> inRadiusCells(uu,4,{allowOccupied:true}).map(p=>({...p,dir:cardinalDirFromDelta(p.r-uu.r,p.c-uu.c)})),
          (uu,aim)=> neyla_SwiftShot(uu,aim),
          {aoe:false},
          {cellTargeting:true, castMs:1100}
        )},
        { key:'穿刺狙击', prob:0.60, cond:()=>true, make:()=> skill('穿刺狙击',2,'red','直线6格 穿透 30HP +流血',
          (uu,aimDir)=> aimDir? range_forward_n(uu,6,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,6,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> neyla_PierceSnipe(uu,desc),
          {aoe:true},
          {castMs:1200}
        )},
        { key:'双钩牵制', prob:0.45, cond:()=>true, make:()=> skill('双钩牵制',2,'red','前方3格优先最近：拉近1格并赋予恐惧（-1步）',
          (uu,aimDir)=> aimDir? range_forward_n(uu,3,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,3,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> neyla_DoubleHook(uu,desc),
          {},
          {castMs:1100}
        )},
        { key:'终末之影', prob:0.30, cond:()=>true, make:()=> makeNeylaEndShadowSkill(u) }
      );
    } else {
      F.push(
        { key:'终末之影', prob:0.50, cond:()=>true, make:()=> makeNeylaEndShadowSkill(u) },
        { key:'执行……', prob:0.55, cond:()=>true, make:()=> skill('执行……',2,'red','前方整排 20伤/20伤（第二枪<15%处决）；自身第一枪-15HP，第二枪-15HP-40SP',
          (uu,aimDir)=> aimDir? range_line(uu,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_line(uu,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> neyla_ExecuteHarpoons(uu,desc),
          {aoe:true},
          {castMs:1800}
        )}
      );
    }
  } else if(u.id==='kyn'){
    if(!u.oppression){
      F.push(
        { key:'迅影突刺', prob:0.60, cond:()=>true, make:()=> skill('迅影突刺',1,'green','5x5内任一敌人身边 20HP（≤25%处决，处决后返身）',
          (uu)=> range_square_n(uu,2),
          (uu,aim)=>{ const tu=getUnitAt(aim.r,aim.c); if(tu && tu.side!=='enemy') kyn_ShadowDash(uu,tu); },
          {aoe:false},
          {cellTargeting:true, castMs:1200}
        )},
        { key:'死亡宣告', prob:0.25, cond:()=>true, make:()=> skill('死亡宣告',3,'red','单体 50HP+30SP（≤30%处决，处决后返身）',
          (uu)=> inRadiusCells(uu,6,{allowOccupied:true}).map(p=>({...p,dir:uu.facing})),
          (uu,aim)=>{ const tu=getUnitAt(aim.r,aim.c); if(tu && tu.side!=='enemy') kyn_DeathCall(uu,tu); },
          {aoe:false},
          {cellTargeting:true, castMs:1200}
        )},
        { key:'割喉飞刃', prob:0.40, cond:()=>true, make:()=> skill('割喉飞刃',2,'red','4格内单体 20HP +流血1 +恐惧1',
          (uu,aimDir,aimCell)=> inRadiusCells(uu,4,{allowOccupied:true}).map(p=>({...p,dir:uu.facing})),
          (uu,aim)=> kyn_ThroatBlade(uu,aim),
          {aoe:false},
          {cellTargeting:true, castMs:900}
        )},
        { key:'影杀之舞', prob:0.50, cond:()=>true, make:()=> skill('影杀之舞',2,'red','3x3 AOE 30HP（不受掩体）并立刻免费位移1格（常态）',
          (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
          (uu)=> kyn_ShadowDance_AOE(uu),
          {aoe:true},
          {castMs:1200}
        )}
      );
    } else {
      F.push(
        { key:'自我了断。。', prob:0.40, cond:()=>true, make:()=> skill('自我了断。。',2,'red','5x5内任意敌人：瞬杀，自己HP清零（压迫）',
          (uu)=> range_square_n(uu,2),
          (uu,aim)=>{ const tu=getUnitAt(aim.r,aim.c); if(tu && tu.side!=='enemy'){ damageUnit(tu.id, tu.hp, 0, `${uu.name} 自我了断 秒杀 ${tu.name}`, uu.id,{skillFx:'kyn:自我了断。。'}); damageUnit(uu.id, uu.hp, 0, `${uu.name} 生命燃尽`, uu.id, {ignoreToughBody:true, skillFx:'kyn:自我了断。。', skillFxCtx:{target:uu}}); } unitActed(uu); },
          {aoe:false},
          {cellTargeting:true, castMs:1100}
        )}
      );
    }
  } else if(u.id==='lirathe'){
    // Lirathe Phase 1 (before transformation)
    if(!u._transformed){
      F.push(
        { key:'刺斩', prob:0.80, cond:()=>true, make:()=> skill('刺斩',1,'red','上下左右冲刺4格，对最后一个敌人造成15HP并上脆弱Debuff',
          (uu,aimDir)=> aimDir? range_forward_n(uu,4,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,4,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> lirathe_DashSlash(uu,desc),
          {aoe:true},
          {castMs:1100}
        )},
        { key:'又想逃？', prob:0.40, cond:()=>true, make:()=> skill('又想逃？',2,'blue','移动任意2格（贴墙则4格），对相邻敌人造成5HP',
          (uu)=> {
            const nearWall = range_adjacent(uu).some(p=> !clampCell(p.r+DIRS[p.dir].dr, p.c+DIRS[p.dir].dc));
            return range_move_radius(uu, nearWall ? 4 : 2);
          },
          (uu,payload)=> lirathe_EscapeMove(uu,payload),
          {},
          {moveSkill:true, moveRadius:4, castMs:800}
        )},
        { key:'刀光吸入', prob:0.40, cond:()=>true, make:()=> skill('刀光吸入',2,'red','前方3x2横扫20伤并上刀光（10层爆炸造成5HP/5SP/层并恢复自身）',
          (uu,aimDir)=> aimDir? forwardRectCentered(uu,aimDir,3,2) : (()=>{const a=[]; for(const d in DIRS) forwardRectCentered(uu,d,3,2).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> lirathe_BladeAbsorb(uu,desc),
          {aoe:true},
          {castMs:1200}
        )},
        { key:'剑舞', prob:0.25, cond:()=>true, make:()=> skill('剑舞',3,'red','多段攻击：前方3x2横扫→反向横扫→3x3→5x5→7x7，全命中上戏谑Buff',
          (uu,aimDir)=> aimDir? forwardRectCentered(uu,aimDir,3,2) : (()=>{const a=[]; for(const d in DIRS) forwardRectCentered(uu,d,3,2).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> lirathe_SwordDance(uu,desc),
          {aoe:true},
          {castMs:2400}
        )}
      );
      // Unlocked after HP <= 50%
      const hpPct = u.hp / u.maxHp;
      if(hpPct <= 0.5){
        F.push(
          { key:'飞溅刀光', prob:0.25, cond:()=>true, make:()=> skill('飞溅刀光',3,'red','前方整排飞溅刀光三段：15HP+刀光→全排15HP+刀光→贯穿5HP+刀光',
            (uu,aimDir)=> aimDir? range_line(uu,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_line(uu,d).forEach(x=>a.push(x)); return a;})(),
            (uu,desc)=> lirathe_SplashBlade(uu,desc),
            {aoe:true},
            {castMs:1800}
          )},
          { key:'别跑', prob:0.40, cond:()=>true, make:()=> skill('别跑',2,'red','前方整排蛛网15SP伤害，50%禁锢（无法移动但可用技能）',
            (uu,aimDir)=> aimDir? range_line(uu,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_line(uu,d).forEach(x=>a.push(x)); return a;})(),
            (uu,desc)=> lirathe_DontRun(uu,desc),
            {aoe:true},
            {castMs:1200}
          )}
        );
      }
    } else {
      // Lirathe Phase 2 (after transformation)
      F.push(
        { key:'冲杀', prob:0.75, cond:()=>true, make:()=> skill('冲杀',2,'red','向前冲刺到底，撞到的敌人20HP/10SP+腐蚀，摧毁掩体',
          (uu,aimDir)=> aimDir? range_line(uu,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_line(uu,d).forEach(x=>a.push(x)); return a;})(),
          (uu,desc)=> lirathe_ChargeKill(uu,desc),
          {aoe:true},
          {castMs:1200}
        )},
        { key:'你在哪', prob:0.30, cond:()=>true, make:()=> skill('你在哪',2,'red','6x6吼叫10SP+腐蚀+看见（下回合结束消失）',
          (uu)=> range_square_n(uu,3),
          (uu)=> lirathe_WhereAreYou(uu),
          {aoe:true},
          {castMs:1200}
        )},
        { key:'掏心掏肺', prob:0.25, cond:()=>true, make:()=> skill('掏心掏肺',2,'red','前方2x2反复撕扯三次15HP/5SP+腐蚀（>5层腐蚀再重复）',
          (uu,aimDir)=> {
            const cells=[];
            for(const d in DIRS){
              const dir=d;
              for(let dr=0;dr<=1;dr++){
                for(let dc=0;dc<=1;dc++){
                  const rr=uu.r+DIRS[dir].dr+dr, cc=uu.c+DIRS[dir].dc+dc;
                  if(clampCell(rr,cc)) cells.push({r:rr,c:cc,dir});
                }
              }
            }
            return cells;
          },
          (uu,desc)=> lirathe_RipHeart(uu,desc),
          {aoe:true},
          {castMs:1800}
        )},
        { key:'找不到路', prob:0.25, cond:()=>true, make:()=> skill('找不到路',3,'red','四个方向冲刺各20HP/10SP+腐蚀',
          (uu)=>[{r:uu.r,c:uu.c,dir:uu.facing}],
          (uu)=> lirathe_CantFindWay(uu),
          {aoe:true},
          {castMs:2400}
        )}
      );
    }
  } else if(u.id && u.id.startsWith('consciousness_')){
    // Consciousness Flower skills
    F.push(
      { key:'抵抗', prob:1.0, cond:()=>true, make:()=> skill('抵抗',1,'green','向前3格刺去造成15HP及5SP',
        (uu,aimDir)=> aimDir? range_forward_n(uu,3,aimDir) : (()=>{const a=[]; for(const d in DIRS) range_forward_n(uu,3,d).forEach(x=>a.push(x)); return a;})(),
        (uu,desc)=> consciousFlower_Resist(uu,desc),
        {},
        {castMs:900}
      )}
    );
  }
  
  // Filter skills based on selection if character is level 50+
  const selectedKeys = getSelectedSkillKeysForUnit(u);
  if (selectedKeys) {
    const filtered = F.filter(factory => selectedKeys.has(factory.key));
    // Only apply filter if at least some skills are selected
    if (filtered.length > 0) {
      return filtered;
    }
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
    checkHazComebackStatus();
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
    checkHazComebackStatus();
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
      
      // Add visual indicator for healing tiles
      const tileKey = `${r},${c}`;
      if(window._healingTiles && window._healingTiles.has(tileKey)){
        cell.classList.add('healing-tile');
        const healIcon = document.createElement('div');
        healIcon.className = 'tile-icon';
        healIcon.textContent = '✚';
        healIcon.style.cssText = 'position:absolute; inset:0; display:flex; align-items:center; justify-content:center; font-size:32px; color:#52c41a; pointer-events:none; text-shadow:0 0 8px #52c41a;';
        cell.appendChild(healIcon);
      }
      
      // Add visual indicator for weakness tiles
      if(window._weaknessTiles && window._weaknessTiles.has(tileKey)){
        cell.classList.add('weakness-tile');
        const weakIcon = document.createElement('div');
        weakIcon.className = 'tile-icon';
        weakIcon.textContent = '⚠';
        weakIcon.style.cssText = 'position:absolute; inset:0; display:flex; align-items:center; justify-content:center; font-size:32px; color:#ff4d4f; pointer-events:none; text-shadow:0 0 8px #ff4d4f;';
        cell.appendChild(weakIcon);
      }
      
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
    if(u.id==='haz'){ div.classList.add('haz-glow'); if(u._comeback) div.classList.add('comeback'); }
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
    const spPct = Math.max(0, Math.min(100, (u.maxSp ? (u.sp/u.maxSp*100) : 0)));
    div.innerHTML = `
      <div>${u.name}</div>
      <div class="hpbar"><div class="hpfill" style="width:${hpPct}%"></div></div>
      <div class="spbar"><div class="spfill" style="width:${spPct}%"></div></div>
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
  const spPct = Math.max(0, Math.min(100, (u.maxSp ? (u.sp/u.maxSp*100) : 0)));

  overlay.innerHTML = `
    <div class="title">${u.name}</div>
    <div class="hpbar"><div class="hpfill" style="width:${hpPct}%"></div></div>
    <div class="spbar"><div class="spfill" style="width:${spPct}%"></div></div>
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
  if(u.status.hazBleedTurns>0) parts.push(`Haz流血x${u.status.hazBleedTurns}`);
  if(u.status.bloodyBud>0) parts.push(`血色花蕾x${u.status.bloodyBud}`);
  if(u.status.recoverStacks>0) parts.push(`恢复x${u.status.recoverStacks}`);
  if(u.status.jixueStacks>0) parts.push(`鸡血x${u.status.jixueStacks}`);
  if(u.status.dependStacks>0) parts.push(`依赖x${u.status.dependStacks}`);
  if(u.status.agileStacks>0) parts.push(`灵活x${u.status.agileStacks}`);
  if(u.status.affirmationStacks>0) parts.push(`肯定x${u.status.affirmationStacks}`);
  if(u.status.mockeryStacks>0) parts.push(`戏谑x${u.status.mockeryStacks}`);
  if(u.status.violenceStacks>0) parts.push(`暴力x${u.status.violenceStacks}`);
  if(u._spBroken) parts.push(`SP崩溃`);
  if(u._spCrashVuln) parts.push('SP崩溃易伤');
  if(hazMarkedTargetId && u.id === hazMarkedTargetId) parts.push('猎杀标记');
  if(u._stanceType && u._stanceTurns>0){
    parts.push(u._stanceType==='defense' ? `防御姿态(${u._stanceTurns})` : `反伤姿态(${u._stanceTurns})`);
  }
  // Display equipped accessory
  if(u.side === 'player'){
    const equipped = loadEquippedAccessories();
    const accessoryId = equipped[u.id];
    if(accessoryId){
      const accessoryNames = {
        bandage: '绷带',
        stimulant: '兴奋剂',
        vest: '防弹衣',
        wine: '白酒',
        tetanus: '破伤风',
        tutorial: '教程'
      };
      const name = accessoryNames[accessoryId] || accessoryId;
      parts.push(`[配件:${name}]`);
    }
  }
  return parts.join(' ');
}
function renderStatus(){
  if(!partyStatus) return;
  partyStatus.innerHTML='';
  for(const id of ['adora','dario','karma','adora_phantom','dario_phantom']){
    const u=units[id]; if(!u || u.hp <= 0) continue;
    const el=document.createElement('div'); el.className='partyRow';
    el.innerHTML=`<strong>${u.name}</strong> HP:${u.hp}/${u.maxHp} SP:${u.sp}/${u.maxSp} ${summarizeNegatives(u)}`;
    partyStatus.appendChild(el);
  }
  const enemyWrap=document.createElement('div'); enemyWrap.style.marginTop='10px'; enemyWrap.innerHTML='<strong>敌方（七海作战队）</strong>';
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
  if(u.passives && u.passives.includes('rooted')) return false; // 根深蒂固被动：无法移动
  if(u.id === 'lirathe' && u._transformed) return false; // Lirathe Phase 2: 失去普通移动能力
  return true;
}
function showDistanceDisplay(r, c, distance){
  clearDistanceDisplay();
  ensureFxLayer();
  const p = getCellCenter(r, c);
  const el = document.createElement('div');
  el.className = 'fx distance-display';
  el.textContent = `距离: ${distance}`;
  el.style.left = `${p.x}px`;
  el.style.top = `${p.y - 30}px`;
  el.style.transform = 'translate(-50%, -100%)';
  el.style.position = 'absolute';
  el.style.background = 'rgba(0,0,0,0.75)';
  el.style.color = '#fff';
  el.style.padding = '4px 8px';
  el.style.borderRadius = '4px';
  el.style.fontSize = '12px';
  el.style.fontWeight = 'bold';
  el.style.pointerEvents = 'none';
  el.style.zIndex = '1000';
  fxLayer.appendChild(el);
  _distanceDisplay = el;
}
function clearDistanceDisplay(){
  if(_distanceDisplay){
    _distanceDisplay.remove();
    _distanceDisplay = null;
  }
}
function clearSkillAiming(){ _skillSelection=null; clearHighlights(); clearDistanceDisplay(); }
function clearAllSelection(){ _skillSelection=null; selectedUnitId=null; clearHighlights(); clearDistanceDisplay(); if(skillPool) skillPool.innerHTML=''; if(selectedInfo) selectedInfo.innerHTML=''; }
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
  clearDistanceDisplay();
  const aimDir = resolveAimDirForSkill(u, sk, aimCell);
  const cells = sk.rangeFn(u, aimDir, aimCell) || [];
  for(const c of cells) markCell(c.r,c.c,'skill');
  const inPreview = rangeIncludeCell(cells, aimCell);
  if(inPreview) {
    markCell(aimCell.r, aimCell.c, 'target');
    // Show distance for assassination skill
    if(sk.name === '课本知识：刺杀一') {
      const dist = mdist(u, aimCell);
      showDistanceDisplay(aimCell.r, aimCell.c, dist);
      // Show spiral effect similar to "呀！你不要靠近我呀！！"
      showSkillFx('adora:呀！你不要靠近我呀！！', {cell: aimCell});
    }
  }
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
function handleSkillConfirmCell(u, sk, aimCell){
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
    if(sk.meta && sk.meta.moveSkill) sk.execFn(u, {moveTo: aimCell});
    else if(sk.meta && sk.meta.cellTargeting) sk.execFn(u, aimCell);
    else if(sk.estimate && sk.estimate.aoe) sk.execFn(u, {dir:aimDir});
    else if(targetUnit) sk.execFn(u, targetUnit);
    else sk.execFn(u, {r:aimCell.r,c:aimCell.c,dir:aimDir});
  }catch(e){ console.error('技能执行错误',e); appendLog(`[错误] 技能执行失败：${sk.name} - ${e.message}`); }

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

  const key=`${r},${c}`; if(!highlighted.has(key)) return;
  if(playerSteps<=0 && sel.side==='player'){ appendLog('剩余步数不足'); return; }
  const occ=getUnitAt(r,c); if(occ){ appendLog('格子被占用'); return; }

  if(sel.size===2){ if(!canPlace2x2(sel, r, c)){ appendLog('该位置无法容纳 2x2 单位'); return; } }

  const moveDir = cardinalDirFromDelta(r - sel.r, c - sel.c);
  setUnitFacing(sel, moveDir);
  sel.r=r; sel.c=c;
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

// —— 回合与被动（含“恢复”/Neyla 保底/姿态结算） —— 

// —— Accessory System ——
function loadEquippedAccessories() {
  if (typeof localStorage === "undefined") return { adora: null, karma: null, dario: null };
  const saved = localStorage.getItem("gwdemo_equipped_accessories");
  return saved ? JSON.parse(saved) : { adora: null, karma: null, dario: null };
}

function applyAccessoryEffects(u, side) {
  if (side !== "player" || !u || u.hp <= 0) return;
  const equipped = loadEquippedAccessories();
  const accessoryId = equipped[u.id];
  if (!accessoryId) return;
  const turnCount = u.turnsStarted || 0;
  
  if (accessoryId === "bandage") {
    const beforeHp = u.hp; const beforeSp = u.sp;
    u.hp = Math.min(u.maxHp, u.hp + 15);
    u.sp = Math.min(u.maxSp, u.sp + 15);
    syncSpBroken(u); showGainFloat(u, u.hp - beforeHp, u.sp - beforeSp);
    appendLog(`${u.name} 的"绷带"：+15HP +15SP`);
    const currentStacks = u.status.recoverStacks || 0;
    updateStatusStacks(u, "recoverStacks", currentStacks + 1, { label: "恢复", type: "buff" });
  }
  
  if (accessoryId === "stimulant" && turnCount % 2 === 0) {
    const currentStacks = u.status.violenceStacks || 0;
    updateStatusStacks(u, "violenceStacks", currentStacks + 1, { label: "暴力", type: "buff" });
    appendLog(`${u.name} 的"兴奋剂"：+1 暴力层数`);
  }
  
  if (accessoryId === "wine") {
    const currentAgility = u.status.agileStacks || 0;
    if (currentAgility < 5) {
      updateStatusStacks(u, "agileStacks", currentAgility + 1, { label: "灵活", type: "buff" });
      appendLog(`${u.name} 的"白酒"：+1 灵活层数`);
    }
  }
  
  if (accessoryId === "tutorial") {
    const beforeSp = u.sp;
    u.sp = Math.min(u.maxSp, u.sp + 10);
    syncSpBroken(u); showGainFloat(u, 0, u.sp - beforeSp);
    appendLog(`${u.name} 的"自我激励教程"：+10SP`);
    
    // 每3回合增加一层肯定Buff
    u.tutorialTurnCount = (u.tutorialTurnCount || 0) + 1;
    if (u.tutorialTurnCount >= 3) {
      u.tutorialTurnCount = 0;
      addStatusStacks(u,'affirmationStacks',1,{label:'肯定', type:'buff'});
      appendLog(`${u.name} 的"自我激励教程"：+1 层肯定Buff`);
    }
  }
}


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
  if(side==='enemy'){
    if(roundsPassed % 2 === 0){
      const haz = units['haz'];
      if(haz && haz.hp>0){ haz.sp = Math.min(haz.maxSp, haz.sp+10); syncSpBroken(haz); showGainFloat(haz,0,10); appendLog('队员们听令！Haz +10SP'); }
      for(const id in units){
        const v=units[id]; if(v.team==='seven' && v.hp>0 && v.id!=='haz'){ v.sp = Math.min(v.maxSp, v.sp+5); syncSpBroken(v); showGainFloat(v,0,5); }
      }
      appendLog('队员们听令！其他队员 +5SP');
    }
    if(roundsPassed >= 20){
      for(const id of ['katz','tusk','neyla','kyn']){
        const v=units[id];
        if(v && v.hp>0 && !v.oppression){
          v.oppression = true;
          v.skillPool.length = 0;
          v.dealtStart = false;
          ensureStartHand(v);
          if(v.id==='neyla') ensureNeylaEndShadowGuarantee(v);
          appendLog(`${v.name} 获得“队长的压迫”：开始使用禁忌技能`);
        }
      }
    }
  }

  for(const id in units){
    const u=units[id];
    if(u.side!==side || u.hp<=0) continue;

    u.actionsThisTurn = 0;
    u.turnsStarted = (u.turnsStarted||0) + 1;
    u._tutorialSpImmuneUsed = false;
    applyAccessoryEffects(u, side);

    const extraDraw = Math.max(0, u.turnsStarted);
    if(extraDraw>0) drawSkills(u, extraDraw);

    // Neyla 压迫后每回合保证“终末之影”在手牌，且最多一张
    if(u.id==='neyla' && u.oppression){ ensureNeylaEndShadowGuarantee(u); }

    // 姿态：回合开始时结算SP恢复与持续回合-1；结束时主动清除
    
    // Check healing tiles for player units
    if(side==='player'){
      checkHealingTiles();
      checkWeaknessTiles();
    }
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
      let val = Math.min(u.maxSp, u.spPendingRestore);
      // Dario quickAdjust passive: Additional 25% SP restore
      if((u.id==='dario' || u.id==='dario_phantom') && u.passives.includes('quickAdjust')){
        val = Math.min(u.maxSp, Math.floor(val * 1.25));
        appendLog(`${u.name} 的"快速调整"触发：额外恢复 25% SP`);
      }
      u.sp = val; syncSpBroken(u); u.spPendingRestore = null;
      appendLog(`${u.name} 的 SP 自动恢复至 ${val}`); showGainFloat(u,0,val);
      if(u.id==='haz'){
        const heal = Math.max(1, Math.floor(u.maxHp*0.05));
        u.hp = Math.min(u.maxHp, u.hp + heal);
        appendLog(`Haz 因SP恢复同时回复 ${heal} HP`); showGainFloat(u,heal,0);
      }
    }

    // “恢复”
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
    if(u.status.hazBleedTurns && u.status.hazBleedTurns>0){
      const bleedDmg = Math.max(1, Math.floor(u.maxHp*0.03));
      damageUnit(u.id, bleedDmg, 0, `${u.name} 因Haz流血受损`, null);
      u.status.hazBleedTurns = Math.max(0, u.status.hazBleedTurns-1);
    }

    // 意识花苞 "恢复" 被动：3回合内未受伤则恢复20HP
    if(u.passives && u.passives.includes('recovery')){
      if(u._lastDamagedRound !== undefined && roundsPassed - u._lastDamagedRound >= 3){
        const before = u.hp;
        u.hp = Math.min(u.maxHp, u.hp + 20);
        showGainFloat(u, u.hp - before, 0);
        appendLog(`${u.name} 的"恢复"被动触发：+20HP`);
      }
    }

    // 老的堡垒兼容（现在已由姿态系统取代）
    if(u.id==='tusk' && u._fortressTurns>0){
      u.sp = Math.min(u.maxSp, u.sp+10);
      syncSpBroken(u);
      showGainFloat(u,0,10);
      u._fortressTurns--;
    }
  }

  checkHazComebackStatus();
}
function processUnitsTurnEnd(side){
  for(const id in units){
    const u=units[id];
    if(u.side!==side) continue;
    if((u.id==='adora' || u.id==='adora_phantom') && u.passives.includes('calmAnalysis')){
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
      // Clear weakness vulnerability when stun ends
      if(u.id === 'lirathe' && next === 0 && u._weaknessVulnerable){
        u._weaknessVulnerable = false;
        appendLog(`${u.name} 恢复正常`);
      }
    }
  }
}
function applyEndOfRoundPassives(){
  // Check both adora and adora_phantom for proximity heal
  for(const adoraId of ['adora', 'adora_phantom']){
    const adora = units[adoraId];
    if(adora && adora.hp>0 && adora.passives.includes('proximityHeal')){
      for(const oid in units){
        const v=units[oid];
        if(!v || v.id===adora.id || v.side!==adora.side || v.hp<=0) continue;
        if(Math.max(Math.abs(v.r-adora.r), Math.abs(v.c-adora.c)) <= 3){
          const heal = Math.max(1, Math.floor(v.maxHp*0.05));
          v.hp = Math.min(v.maxHp, v.hp + heal);
          v.sp = Math.min(v.maxSp, v.sp + 5);
          syncSpBroken(v);
          appendLog(`${adora.name} 邻近治疗：为 ${v.name} 恢复 ${heal} HP 和 5 SP`);
          showGainFloat(v,heal,5);
        }
      }
    }
  }
}
// —— Lirathe Phase 2 Helper Functions ——
async function triggerLiratheFinalPhase(){
  const lirathe = units['lirathe'];
  const karma = units['karma'];
  const adora_phantom = units['adora_phantom'];
  const dario_phantom = units['dario_phantom'];
  
  if(!lirathe || lirathe.hp<=0) return;
  
  interactionLocked = true;
  
  // Restore Lirathe to full HP
  lirathe.hp = lirathe.maxHp;
  lirathe.status = {}; // Clear all debuffs
  
  // Adora and Dario phantoms HP→1, add 99 corrosion
  if(adora_phantom && adora_phantom.hp>0){
    adora_phantom.hp = 1;
    if(!adora_phantom.status.corrosionStacks) adora_phantom.status.corrosionStacks = 0;
    adora_phantom.status.corrosionStacks = 99;
    updateStatusStacks(adora_phantom,'corrosionStacks',99,{label:'腐蚀',type:'debuff'});
  }
  if(dario_phantom && dario_phantom.hp>0){
    dario_phantom.hp = 1;
    if(!dario_phantom.status.corrosionStacks) dario_phantom.status.corrosionStacks = 0;
    dario_phantom.status.corrosionStacks = 99;
    updateStatusStacks(dario_phantom,'corrosionStacks',99,{label:'腐蚀',type:'debuff'});
  }
  
  // Lock Karma to 1 HP
  if(karma){
    karma._lockedMinHp = 1;
  }
  
  appendLog('=====================');
  appendLog('Lirathe 最终阶段！');
  appendLog('=====================');
  
  renderAll();
  
  // Pause 3 seconds
  await aiAwait(3000);
  
  // Teleport Lirathe to Karma's side
  if(karma && karma.hp>0){
    const adj = range_adjacent(karma);
    if(adj.length>0){
      lirathe.r = adj[0].r;
      lirathe.c = adj[0].c;
    }
  }
  
  renderAll();
  
  // Use 掏心掏肺 7 times
  for(let i=0;i<7;i++){
    if(lirathe.hp<=0) break;
    await lirathe_RipHeart(lirathe, {dir:lirathe.facing});
    await aiAwait(800);
  }
  
  // Show dialogue
  await showLiratheDialog();
  
  // Permanent stun
  lirathe.status.stunned = 999;
  lirathe._permanentStun = true;
  appendLog('Lirathe 进入永久眩晕状态');
  
  // Stop spawning
  lirathe._stopSpawning = true;
  
  // Remove all consciousness flowers
  for(const id in units){
    if(id.startsWith('consciousness_') && units[id] && units[id].hp>0){
      units[id].hp = 0;
    }
  }
  
  // Clear healing tiles
  if(window._healingTiles){
    window._healingTiles.clear();
  }
  
  // Clear weakness tiles
  if(window._weaknessTiles){
    window._weaknessTiles.clear();
  }
  
  interactionLocked = false;
  renderAll();
}

async function showLiratheDialog(){
  const dialogBox = document.createElement('div');
  dialogBox.style.cssText = 'position:fixed;top:50%;left:50%;transform:translate(-50%,-50%);background:rgba(0,0,0,0.95);color:#fff;padding:50px;border-radius:15px;max-width:700px;z-index:10000;font-size:20px;line-height:2.2;box-shadow:0 10px 40px rgba(0,0,0,0.8);';
  
  dialogBox.innerHTML = `
    <div style="text-align:center;">
      <p style="color:#aaa;font-size:18px;">（Lirathe即将杀掉Karma时，看到了周围血坑中的倒影）</p>
      <p style="color:#aaa;font-size:18px;margin-top:10px;">（和女孩子没有任何关系的自己）</p>
      <p style="color:#ff6b6b;margin-top:30px;font-size:22px;">Lirathe：（我在干什么。。。）</p>
      <p style="color:#ff6b6b;font-size:22px;">Lirathe：（我为什么会变成这样）</p>
      <p style="color:#ff6b6b;font-size:22px;">Lirathe：（。。。。）</p>
      <p style="color:#ff6b6b;margin-bottom:35px;font-size:22px;">Lirathe：（抱歉。。）</p>
      <button id="dialogConfirm" style="padding:12px 40px;font-size:18px;background:#4a90e2;border:none;color:#fff;border-radius:8px;cursor:pointer;box-shadow:0 4px 12px rgba(74,144,226,0.4);">确定</button>
    </div>
  `;
  
  document.body.appendChild(dialogBox);
  
  return new Promise(resolve => {
    document.getElementById('dialogConfirm').onclick = () => {
      dialogBox.remove();
      resolve();
    };
  });
}

function spawnConsciousnessfollower(){
  const empty = [];
  for(let r=1;r<=ROWS;r++){
    for(let c=1;c<=COLS;c++){
      if(clampCell(r,c) && !getUnitAt(r,c)) empty.push({r,c});
    }
  }
  if(empty.length === 0) return;
  
  const pos = empty[Math.floor(Math.random() * empty.length)];
  const id = 'consciousness_' + Date.now();
  units[id] = createUnit(id,'意识花苞','enemy',50, pos.r, pos.c, 150,0, 0,0, ['rooted','recovery','limitedAction']);
  units[id]._lastDamagedRound = -999;
  ensureStartHand(units[id]);
  appendLog('意识花苞出现了！');
  renderAll();
}

function spawnHealingTile(){
  const empty = [];
  for(let r=1;r<=ROWS;r++){
    for(let c=1;c<=COLS;c++){
      if(clampCell(r,c) && !getUnitAt(r,c)) empty.push({r,c});
    }
  }
  if(empty.length === 0) return;
  
  const pos = empty[Math.floor(Math.random() * empty.length)];
  // Mark this cell as a healing tile
  if(!window._healingTiles) window._healingTiles = new Set();
  window._healingTiles.add(`${pos.r},${pos.c}`);
  appendLog(`小恢复格子出现在 (${pos.r},${pos.c})！`);
  renderAll();
}

function checkHealingTiles(){
  if(!window._healingTiles) return;
  
  for(const id in units){
    const u = units[id];
    if(u && u.hp>0 && u.side==='player'){
      const key = `${u.r},${u.c}`;
      if(window._healingTiles.has(key)){
        u.hp = Math.min(u.maxHp, u.hp + 50);
        u.sp = Math.min(u.maxSp, u.sp + 50);
        showDamageFloat(u, -50, -50);
        appendLog(`${u.name} 踩到小恢复格子：恢复50HP/50SP`);
        window._healingTiles.delete(key);
        renderAll();
      }
    }
  }
}

function createWeaknessTile(r, c){
  if(!window._weaknessTiles) window._weaknessTiles = new Set();
  window._weaknessTiles.add(`${r},${c}`);
  appendLog(`软肋格子出现在 (${r},${c})！`);
  renderAll();
}

function checkWeaknessTiles(){
  if(!window._weaknessTiles) return;
  const lirathe = units['lirathe'];
  if(!lirathe || lirathe.hp <= 0 || !lirathe._transformed) return;
  
  for(const id in units){
    const u = units[id];
    if(u && u.hp>0 && u.side==='player'){
      const key = `${u.r},${u.c}`;
      if(window._weaknessTiles.has(key) && lirathe._highGround){
        // Lirathe falls down
        lirathe._highGround = false;
        addStatusStacks(lirathe, 'stunned', 1, {label:'眩晕', type:'debuff'});
        lirathe._weaknessVulnerable = true; // Take 50% more damage
        appendLog(`${u.name} 踩到软肋格子：Lirathe 从高处掉落并眩晕！`);
        window._weaknessTiles.delete(key);
        renderAll();
      }
    }
  }
}

function finishEnemyTurn(){
  clearAIWatchdog();
  processUnitsTurnEnd('enemy');
  roundsPassed += 1;
  
  // Round 2: Spawn Adora and Dario phantoms
  if(roundsPassed === 2 && !units['adora_phantom']){
    units['adora_phantom'] = createUnit('adora_phantom','Adora（虚影）','player',50, 5, 20, 100,100, 0.5,20, ['calmAnalysis','fearBuff','proximityHeal','backstab']);
    units['dario_phantom'] = createUnit('dario_phantom','Dario（虚影）','player',50, 5, 24, 150,100, 0.75,20, ['quickAdjust','counterattack','moraleBoost']);
    
    ensureStartHand(units['adora_phantom']);
    ensureStartHand(units['dario_phantom']);
    
    appendLog('第2回合：Adora和Dario的虚影出现支援Karma！');
    renderAll();
  }
  
  // Lirathe Phase 2 mechanics
  const lirathe = units['lirathe'];
  if(lirathe && lirathe.hp>0 && lirathe._transformed){
    // Consciousness flower spawning (every 5 rounds)
    if(!lirathe._stopSpawning){
      lirathe._consciousnessFlowerRounds = (lirathe._consciousnessFlowerRounds || 0) + 1;
      if(lirathe._consciousnessFlowerRounds >= 5){
        lirathe._consciousnessFlowerRounds = 0;
        spawnConsciousnessfollower();
      }
      
      // Healing tile spawning (every 10 rounds)
      lirathe._healingTileRounds = (lirathe._healingTileRounds || 0) + 1;
      if(lirathe._healingTileRounds >= 10){
        lirathe._healingTileRounds = 0;
        spawnHealingTile();
      }
    }
  }
  
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
      if(canPlace2x2(u, cand.r, cand.c)){ u.r=cand.r; u.c=cand.c; setUnitFacing(u, dir); return {moved:true}; }
    } else {
      if(!getUnitAt(cand.r,cand.c)){ u.r=cand.r; u.c=cand.c; setUnitFacing(u, dir); return {moved:true}; }
    }
  }
  return {moved:false};
}
function computeRallyPoint(){
  const haz = units['haz'];
  if(haz && haz.hp>0) return {r:haz.r, c:haz.c};
  const allies = Object.values(units).filter(x=>x.side==='enemy' && x.hp>0);
  if(allies.length===0) return {r:10,c:10};
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
      const isBuffName = ['锁链缠绕','战争堡垒','拼尽全力保卫队长'].includes(sk.name);
      const canUseBuff = isBuffName && ((sk.name==='锁链缠绕' && en.chainShieldTurns<=0) || (!en._stanceType || en._stanceTurns<=0));
      if(isSelfOnly && isBuffName && canUseBuff){
        candidates.push({sk, dir:en.facing, score: 22}); // 自保最高
        continue;
      }

      const dirs = Object.keys(DIRS);
      const isAdjSkill = ['鱼叉穿刺','骨盾猛击','沙包大的拳头','短匕轻挥'].includes(sk.name);
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
      if(en.id==='neyla' && en.oppression) ensureNeylaEndShadowGuarantee(en);

      // 1) 尝试技能
      let didAct = false;
      
      // limitedAction passive: can only use 1 skill per turn
      if(en.passives && en.passives.includes('limitedAction') && (en.actionsThisTurn||0) >= 1){
        aiLog(en,'limitedAction: 本回合已使用技能，跳过');
      } else {
        const candidates = buildSkillCandidates(en);
        if(candidates.length>0){
          didAct = await execEnemySkillCandidate(en, candidates[0]);
          if(didAct) progressedThisRound = true;
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
  const lirathe = units['lirathe'];
  
  // Lirathe's permanent stun counts as victory
  if(lirathe && lirathe.hp>0 && lirathe._permanentStun){
    showAccomplish();
    return true;
  }
  
  const enemiesAlive = Object.values(units).some(u=>u.side==='enemy' && u.hp>0 && !u._permanentStun);
  const playersAlive = Object.values(units).some(u=>u.side==='player' && u.hp>0);
  if(!enemiesAlive){ showAccomplish(); return true; }
  if(!playersAlive){ 
    appendLog('全灭，失败');
    showDefeatScreen();
    return true; 
  }
  return false;
}
function showAccomplish(){
  if(!accomplish) return;
  // Stop Boss BGM on victory
  stopBossBGM();
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
  if(btn) btn.onclick=()=>{ 
    accomplish.classList.add('hidden'); 
    appendLog('通关!'); 
    
    // Award coins for completing sevenSeas stage
    if (typeof localStorage !== 'undefined') {
      const STORAGE_KEY_COINS = 'gwdemo_coins';
      const STORAGE_KEY_STAGE_COMPLETIONS = 'gwdemo_stage_completions';
      
      // Load current coins and completions
      const currentCoins = parseInt(localStorage.getItem(STORAGE_KEY_COINS) || '0', 10);
      const completions = JSON.parse(localStorage.getItem(STORAGE_KEY_STAGE_COMPLETIONS) || '{"intro":0,"abandonedAnimals":0,"fatigue":0,"sevenSeas":0}');
      
      // Increment sevenSeas completions
      completions.sevenSeas = (completions.sevenSeas || 0) + 1;
      localStorage.setItem(STORAGE_KEY_STAGE_COMPLETIONS, JSON.stringify(completions));
      
      // Award 1 coin
      const newCoins = currentCoins + 1;
      localStorage.setItem(STORAGE_KEY_COINS, newCoins.toString());
      
      appendLog('获得 1 币！（总计: ' + newCoins + ' 币）');
    }
    
    // Return to stage selection after victory
    setTimeout(() => {
      window.location.href = 'index.html';
    }, 500);
  };
}
function showDefeatScreen(){
  // Stop Boss BGM on defeat
  stopBossBGM();
  // Show defeat message and return to stage selection
  const defeatMsg = '战斗失败！即将返回关卡界面...';
  appendLog(defeatMsg);
  
  // Create a simple defeat overlay or use the accomplish modal
  if(accomplish){
    accomplish.classList.remove('hidden');
    const modalContent = accomplish.querySelector('.modal-content');
    if(modalContent){
      modalContent.querySelector('h2').textContent = '战斗失败';
      if(damageSummary) damageSummary.innerHTML = '<p>全军覆没，请重新尝试。</p>';
    }
    const btn=document.getElementById('confirmBtn');
    if(btn){
      btn.textContent = '返回关卡';
      btn.onclick=()=>{ 
        accomplish.classList.add('hidden');
        // Return to stage selection after defeat
        setTimeout(() => {
          window.location.href = 'index.html';
        }, 300);
      };
    }
  } else {
    // Fallback: direct redirect after delay
    setTimeout(() => {
      window.location.href = 'index.html';
    }, 2000);
  }
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
function checkHazComebackStatus(){
  const haz = units['haz'];
  if(!haz || haz.hp<=0) return;
  const others = Object.values(units).filter(v=>v.side==='enemy' && v.hp>0 && v.id!=='haz');
  const shouldActive = (others.length===0);
  if(shouldActive && !haz._comeback){
    haz._comeback = true;

    if(haz.skillPool && haz.skillPool.length){
      haz.skillPool = haz.skillPool.filter(sk => sk.name === '深海猎杀');
    } else {
      haz.skillPool = [];
    }
    const need = Math.max(0, START_HAND_COUNT - haz.skillPool.length);
    drawSkills(haz, need);

    appendLog('Haz 被动「力挽狂澜」觉醒：伤害+10%，所受伤害-10%，卡池已替换为「深海猎杀 + 力挽狂澜禁招」，其他原始技能出现几率为 0');
  }
}

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
  bossBGM = document.getElementById('bossBGM');

  updateCameraBounds();
  createCameraControls();
  registerCameraInputs();
  cameraReset({immediate:true});
  startCameraLoop();

  // 掩体（不可进入）- 旧情未了关卡无掩体

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

  appendLog('旧情未了 Boss 战开始：地图 9x26');
  appendLog('Boss：Lirathe（利拉斯-赫雷西第五干部）- 两阶段战斗');
  appendLog('第2回合时，Adora和Dario将以虚影形式出现支援Karma');
  appendLog('敌方攻击带预警并有较长前摇；AOE 预警为青色、命中为红色；多阶段技能逐段即时结算。');

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
