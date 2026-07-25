/* ============================================================
   Alchemist's Laboratory — app logic
   Ports the Brew Lab math (mixing, techniques, nearest-potion
   matching, and recipe search) from the original notebook into
   plain JavaScript, plus the UI that drives it.
   ============================================================ */

const STAT_NAMES = ['Humor','Vigor','Lucidity','Natura','Weave','Flux','Aether','Calor'];
const RARITY_ORDER = ['Common','Uncommon','Rare','Very Rare','Legendary','Artifice'];
const rarityNum = (r) => RARITY_ORDER.indexOf(r) + 1; // 1-indexed, -1 => 0 if unknown

/* ---------------- vector / matrix helpers (8-dim) ---------------- */
function vAdd(a,b){ return a.map((x,i)=>x+b[i]); }
function vScale(a,s){ return a.map(x=>x*s); }
function vSub(a,b){ return a.map((x,i)=>x-b[i]); }
function dot(a,b){ return a.reduce((s,x,i)=>s+x*b[i],0); }
function norm(a){ return Math.sqrt(dot(a,a)); }
function vSum(vectors){
  const out = new Array(8).fill(0);
  for(const v of vectors){ for(let i=0;i<8;i++) out[i]+=v[i]; }
  return out;
}
function outer(a,b){
  const R=[];
  for(let i=0;i<a.length;i++){
    const row=[];
    for(let j=0;j<b.length;j++) row.push(a[i]*b[j]);
    R.push(row);
  }
  return R;
}
function matSub(A,B){ return A.map((row,i)=>row.map((x,j)=>x-B[i][j])); }
function matAdd(A,B){ return A.map((row,i)=>row.map((x,j)=>x+B[i][j])); }
function matScale(A,s){ return A.map(row=>row.map(x=>x*s)); }
function matMul(A,B){
  const n=A.length, m=B[0].length, k=B.length;
  const R=[];
  for(let i=0;i<n;i++){
    const row=[];
    for(let j=0;j<m;j++){
      let s=0;
      for(let x=0;x<k;x++) s+=A[i][x]*B[x][j];
      row.push(s);
    }
    R.push(row);
  }
  return R;
}
function matVec(A,v){
  return A.map(row=>dot(row,v));
}
function identity(n){
  const I=[];
  for(let i=0;i<n;i++){ const row=new Array(n).fill(0); row[i]=1; I.push(row); }
  return I;
}
function normalize(v){
  const n = norm(v);
  if(n < 1e-12) return v.slice();
  return vScale(v, 1/n);
}

/* Rotate x toward unit vector u by a fraction of the angle between them.
   Faithful port of rotation_toward_unit_fraction from the notebook
   (Rodrigues' rotation restricted to the plane spanned by u and x). */
function rotationTowardUnitFraction(u, x, frac){
  const EPS = 1e-12;
  const uN = normalize(u);
  const nx = norm(x);
  if(nx < EPS) return identity(8);

  const fracUsed = Math.max(0, Math.min(1, frac));
  let cosang = dot(uN, x) / nx;
  cosang = Math.max(-1, Math.min(1, cosang));
  const angle = Math.acos(cosang);
  const theta = -fracUsed * angle;

  const a = dot(uN, x);
  const xPerp = vSub(x, vScale(uN, a));
  const b = norm(xPerp);

  let v;
  if(b < EPS){
    // degenerate: x is parallel to u, pick any orthogonal direction
    let idx = 0, minAbs = Infinity;
    for(let i=0;i<8;i++){ if(Math.abs(uN[i]) < minAbs){ minAbs = Math.abs(uN[i]); idx = i; } }
    const e = new Array(8).fill(0); e[idx] = 1;
    v = vSub(e, vScale(uN, dot(uN,e)));
    const vn = norm(v);
    v = vn < EPS ? e : vScale(v, 1/vn);
  } else {
    v = vScale(xPerp, 1/b);
  }
  // re-orthogonalize against u defensively
  v = vSub(v, vScale(uN, dot(uN, v)));
  const vn2 = norm(v);
  if(vn2 > EPS) v = vScale(v, 1/vn2);

  const I = identity(8);
  const K = matSub(outer(v,uN), outer(uN,v));
  const K2 = matMul(K,K);
  const s = Math.sin(theta), c = Math.cos(theta);
  const R = matAdd(I, matAdd(matScale(K,s), matScale(K2, 1-c)));
  return R;
}

/* ---------------- techniques ---------------- */
const TECHNIQUES = {
  boil_down: {
    label: 'Boil Down',
    hint: 'Reduces the mixture, scaling every essence down to 75%.',
    apply: (v) => vScale(v, 0.75)
  },
  distillation: {
    label: 'Distillation',
    hint: 'The baseline technique — the mixture is used as-is.',
    apply: (v) => v.slice()
  },
  fractional_distillation: {
    label: 'Fractional Distillation',
    hint: 'A more careful reduction, concentrating the mixture to 125%.',
    apply: (v) => vScale(v, 1.25)
  },
  vacuum_distillation: {
    label: 'Vacuum Distillation',
    hint: 'An aggressive concentration, scaling every essence up to 150%.',
    apply: (v) => vScale(v, 1.5)
  },
  poisoners_extraction: {
    label: "Poisoner's Extraction",
    hint: 'Bends the mixture toward Humor/Vigor-negative — harm and debilitation.',
    apply: (v) => matVec(rotationTowardUnitFraction([-1,-1,0,0,0,0,0,0], v, 0.25), v)
  },
  imbibers_infusion: {
    label: "Imbiber's Infusion",
    hint: 'Bends the mixture toward Vigor — vitality and physical prowess.',
    apply: (v) => matVec(rotationTowardUnitFraction([0,1,0,0,0,0,0,0], v, 0.25), v)
  },
  healers_reflux: {
    label: "Healer's Reflux",
    hint: 'Bends the mixture toward Humor — restoration and healing.',
    apply: (v) => matVec(rotationTowardUnitFraction([1,0,0,0,0,0,0,0], v, 0.25), v)
  }
};

/* ---------------- rarity shells ---------------- */
function buildShells(items){
  // returns array indexed 0..5 (Common..Artifice), each a list of items
  const shells = [[],[],[],[],[],[]];
  for(const it of items){
    const idx = rarityNum(it.rarity) - 1;
    if(idx >= 0 && idx < 6) shells[idx].push(it);
  }
  return shells;
}
const ING_SHELLS = buildShells(INGREDIENTS);
const POT_SHELLS = buildShells(POTIONS);

/* ---------------- core brewing ---------------- */
function cmix(recipe, techniqueKey){
  // recipe: array of {item, qty}
  const vectors = [];
  for(const {item, qty} of recipe){
    for(let i=0;i<qty;i++) vectors.push(item.stats);
  }
  const summed = vSum(vectors);
  return TECHNIQUES[techniqueKey].apply(summed);
}

function detPotShell(recipe){
  let maxShell = 1;
  for(const {item} of recipe){
    maxShell = Math.max(maxShell, rarityNum(item.rarity));
  }
  return maxShell;
}

// Faithful port of the notebook's search-space selection (including its
// quirk: for ingredient shells above Common, the search space is the two
// potion shells *above* the ingredient shell's own index, not the shell
// itself). See the README note on this.
function searchSpaceForShell(shell){
  if(shell <= 1) return POT_SHELLS[0];
  let space = (POT_SHELLS[shell] || []).concat(POT_SHELLS[shell+1] || []);
  if(space.length === 0){
    // graceful fallback so brewing never dead-ends: widen to all potions
    // at or below the ingredient shell if the "two tiers up" band is empty
    for(let i=shell-1; i>=0 && space.length===0; i--) space = POT_SHELLS[i];
    if(space.length === 0) space = POTIONS;
  }
  return space;
}

function dictBrew(recipe, techniqueKey){
  const netVec = cmix(recipe, techniqueKey);
  const shell = detPotShell(recipe);
  const space = searchSpaceForShell(shell);

  const scored = space.map(pot => ({ pot, dist: norm(vSub(netVec, pot.stats)) }));
  scored.sort((a,b) => a.dist - b.dist);
  return { netVec, shell, scored };
}

/* ---------------- recipe search (Recipe Finder) ---------------- */
function availableIngredientsForTarget(targetPotion){
  const targetShellIdx = rarityNum(targetPotion.rarity) - 1; // 0-indexed
  let pool = [];
  for(let i=0;i<=targetShellIdx && i<6;i++) pool = pool.concat(ING_SHELLS[i]);
  if(pool.length === 0) pool = INGREDIENTS; // fallback if nothing at/below that tier
  return pool;
}

function randomRecipe(pool, count){
  const chosen = [];
  for(let i=0;i<count;i++){
    chosen.push(pool[Math.floor(Math.random()*pool.length)]);
  }
  // collapse into {item, qty} pairs
  const map = new Map();
  for(const item of chosen){
    map.set(item.name, { item, qty: (map.get(item.name)?.qty || 0) + 1 });
  }
  return Array.from(map.values());
}

/* ============================================================
   SVG sigil — the 8-axis glyph used everywhere
   ============================================================ */
let GLOBAL_MAX_ABS = 1;
(function computeGlobalScale(){
  let m = 1;
  for(const it of INGREDIENTS.concat(POTIONS)){
    for(const s of it.stats) m = Math.max(m, Math.abs(s));
  }
  GLOBAL_MAX_ABS = m;
})();

function sigilSVG(stats, {size=64, stroke='#c79a4b', fill='rgba(199,154,75,0.18)', showAxes=true, axisColor='#34304a'} = {}){
  const n = 8;
  const cx = 50, cy = 50, rMax = 42;
  const angleFor = (i) => (Math.PI*2*i/n) - Math.PI/2;

  const axisLines = [];
  const labels = [];
  for(let i=0;i<n;i++){
    const a = angleFor(i);
    const x = cx + rMax*Math.cos(a), y = cy + rMax*Math.sin(a);
    if(showAxes) axisLines.push(`<line x1="${cx}" y1="${cy}" x2="${x.toFixed(2)}" y2="${y.toFixed(2)}" stroke="${axisColor}" stroke-width="0.6"/>`);
  }
  // ring guides
  const rings = showAxes ? [0.33,0.66,1].map(f=>{
    const pts = [];
    for(let i=0;i<n;i++){ const a=angleFor(i); pts.push(`${(cx+rMax*f*Math.cos(a)).toFixed(2)},${(cy+rMax*f*Math.sin(a)).toFixed(2)}`); }
    return `<polygon points="${pts.join(' ')}" fill="none" stroke="${axisColor}" stroke-width="0.5"/>`;
  }).join('') : '';

  const scale = GLOBAL_MAX_ABS || 1;
  const pts = stats.map((v,i)=>{
    const a = angleFor(i);
    const r = Math.max(0, Math.min(1, Math.abs(v)/scale)) * rMax;
    const sign = v < 0 ? -1 : 1; // negative essences plotted, just shorter/same ring — direction stays outward
    const rr = (Math.abs(v)/scale) * rMax;
    const x = cx + rr*Math.cos(a), y = cy + rr*Math.sin(a);
    return `${x.toFixed(2)},${y.toFixed(2)}`;
  }).join(' ');

  return `<svg viewBox="0 0 100 100" xmlns="http://www.w3.org/2000/svg">
    ${rings}
    ${axisLines.join('')}
    <polygon points="${pts}" fill="${fill}" stroke="${stroke}" stroke-width="1.4" stroke-linejoin="round"/>
  </svg>`;
}

function brandMarkSVG(){
  // an abstract sigil for the logo: a balanced 8-point star
  const stats = [1,0.6,0.8,0.5,1,0.4,0.7,0.55].map(x=>x*GLOBAL_MAX_ABS*0.9);
  return sigilSVG(stats, {stroke:'#c79a4b', fill:'rgba(199,154,75,0.22)', axisColor:'#3a3552'});
}

/* ============================================================
   Rendering helpers
   ============================================================ */
function rarityClass(r){ return 'rarity-' + String(r).replace(/\s+/g,'-'); }

function rarityChip(r){
  return `<span class="rarity-chip ${rarityClass(r)}">${r || 'Unknown'}</span>`;
}

function statTable(stats){
  return stats.map((v,i)=>`<div class="stat-row"><span class="stat-name">${STAT_NAMES[i]}</span><span class="stat-val">${v>0?'+':''}${v}</span></div>`).join('');
}

function escapeHtml(str){
  return String(str).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}

/* ============================================================
   Tabs
   ============================================================ */
document.getElementById('tabs').addEventListener('click', (e)=>{
  const btn = e.target.closest('.tab-btn');
  if(!btn) return;
  document.querySelectorAll('.tab-btn').forEach(b=>b.classList.remove('active'));
  btn.classList.add('active');
  const tab = btn.dataset.tab;
  document.querySelectorAll('.panel').forEach(p=>{
    p.classList.toggle('hidden', p.dataset.panel !== tab);
  });
});

/* ============================================================
   Brew Lab
   ============================================================ */
const brewState = { recipe: [] /* {item, qty} */ };

function populateTechniqueSelect(selectEl){
  selectEl.innerHTML = Object.entries(TECHNIQUES).map(([key,t])=>`<option value="${key}">${t.label}</option>`).join('');
}
const techniqueSelect = document.getElementById('techniqueSelect');
populateTechniqueSelect(techniqueSelect);
function updateTechniqueHint(){
  document.getElementById('techniqueHint').textContent = TECHNIQUES[techniqueSelect.value].hint;
}
techniqueSelect.addEventListener('change', updateTechniqueHint);
updateTechniqueHint();

const ingSearchInput = document.getElementById('ingSearch');
const ingPickerResults = document.getElementById('ingPickerResults');
ingSearchInput.addEventListener('input', ()=>{
  const q = ingSearchInput.value.trim().toLowerCase();
  if(!q){ ingPickerResults.innerHTML=''; return; }
  const matches = INGREDIENTS.filter(i=>i.name.toLowerCase().includes(q)).slice(0,25);
  ingPickerResults.innerHTML = matches.map(i=>`
    <div class="picker-item" data-name="${escapeHtml(i.name)}">
      <span class="p-name">${escapeHtml(i.name)}</span>
      <span class="p-rarity">${i.rarity}</span>
    </div>`).join('') || `<div class="picker-item"><span class="p-name">No matches</span></div>`;
});
ingPickerResults.addEventListener('click', (e)=>{
  const row = e.target.closest('.picker-item');
  if(!row || !row.dataset.name) return;
  const item = INGREDIENTS.find(i=>i.name === row.dataset.name);
  if(!item) return;
  const existing = brewState.recipe.find(r=>r.item.name === item.name);
  if(existing) existing.qty += 1;
  else brewState.recipe.push({ item, qty: 1 });
  ingSearchInput.value = '';
  ingPickerResults.innerHTML = '';
  renderRecipeList();
});

function renderRecipeList(){
  const el = document.getElementById('recipeList');
  if(brewState.recipe.length === 0){
    el.innerHTML = `<p class="empty-note">Nothing in the cauldron yet. Add at least two ingredients.</p>`;
    document.getElementById('brewBtn').disabled = false;
    return;
  }
  el.innerHTML = brewState.recipe.map(({item,qty})=>`
    <div class="recipe-row" data-name="${escapeHtml(item.name)}">
      <span class="r-name">${escapeHtml(item.name)}</span>
      <span class="r-qty">
        <button class="qty-btn" data-action="dec">−</button>
        <span>${qty}</span>
        <button class="qty-btn" data-action="inc">+</button>
        <button class="remove-btn" data-action="remove" title="Remove">✕</button>
      </span>
    </div>`).join('');
}
document.getElementById('recipeList').addEventListener('click', (e)=>{
  const btn = e.target.closest('button');
  if(!btn) return;
  const row = e.target.closest('.recipe-row');
  const name = row.dataset.name;
  const entry = brewState.recipe.find(r=>r.item.name===name);
  if(!entry) return;
  if(btn.dataset.action === 'inc') entry.qty += 1;
  if(btn.dataset.action === 'dec') entry.qty = Math.max(1, entry.qty-1);
  if(btn.dataset.action === 'remove') brewState.recipe = brewState.recipe.filter(r=>r.item.name!==name);
  renderRecipeList();
});

document.getElementById('brewBtn').addEventListener('click', ()=>{
  const resultEl = document.getElementById('brewResult');
  const totalQty = brewState.recipe.reduce((s,r)=>s+r.qty, 0);
  if(totalQty < 2){
    resultEl.innerHTML = `<div class="empty-note result-placeholder"><p>Add at least two ingredients before brewing.</p></div>`;
    return;
  }
  const techniqueKey = techniqueSelect.value;
  const { netVec, scored } = dictBrew(brewState.recipe, techniqueKey);
  const best = scored[0];
  const refScale = best.pot.magnitude > 0 ? best.pot.magnitude : (norm(netVec) || 1);
  const matchScore = Math.max(0, 1 - (best.dist / refScale));

  resultEl.innerHTML = `
    <div class="potion-result">
      <div class="result-header">
        <div class="result-sigil">${sigilSVG(best.pot.stats, {stroke:'#9b7fce', fill:'rgba(155,127,206,0.2)'})}</div>
        <div class="result-title">
          <h3>${escapeHtml(best.pot.name)}</h3>
          ${rarityChip(best.pot.rarity)}
        </div>
      </div>
      <div class="result-meta">
        ${best.pot.effect ? `<p>${escapeHtml(best.pot.effect)}</p>` : ''}
        ${best.pot.consumption ? `<p><em>${escapeHtml(best.pot.consumption)}</em>${best.pot.value ? ' · ' + escapeHtml(best.pot.value) : ''}</p>` : ''}
      </div>
      <div class="match-bar-wrap">
        <div class="match-bar-track"><div class="match-bar-fill" style="width:${Math.round(matchScore*100)}%"></div></div>
        <p class="match-label">Match closeness: ${(matchScore*100).toFixed(0)}% (distance ${best.dist.toFixed(2)})</p>
      </div>
      <details class="candidates">
        <summary>Nearest alternatives</summary>
        ${scored.slice(1,4).map(c=>`<div class="candidate-row"><span>${escapeHtml(c.pot.name)}</span><span>${c.dist.toFixed(2)}</span></div>`).join('')}
      </details>
    </div>`;
});

document.getElementById('placeholderSigil').innerHTML = sigilSVG([0,0,0,0,0,0,0,0], {stroke:'#57516f'});
document.getElementById('brandMark').innerHTML = brandMarkSVG();

/* ============================================================
   Recipe Finder
   ============================================================ */
const finderState = { target: null };

populateTechniqueSelect(document.getElementById('finderTechniqueSelect'));

const targetSearchInput = document.getElementById('targetPotionSearch');
const potPickerResults = document.getElementById('potPickerResults');
targetSearchInput.addEventListener('input', ()=>{
  const q = targetSearchInput.value.trim().toLowerCase();
  if(!q){ potPickerResults.innerHTML=''; return; }
  const matches = POTIONS.filter(p=>p.name.toLowerCase().includes(q)).slice(0,25);
  potPickerResults.innerHTML = matches.map(p=>`
    <div class="picker-item" data-name="${escapeHtml(p.name)}">
      <span class="p-name">${escapeHtml(p.name)}</span>
      <span class="p-rarity">${p.rarity}</span>
    </div>`).join('') || `<div class="picker-item"><span class="p-name">No matches</span></div>`;
});
potPickerResults.addEventListener('click', (e)=>{
  const row = e.target.closest('.picker-item');
  if(!row || !row.dataset.name) return;
  const pot = POTIONS.find(p=>p.name===row.dataset.name);
  if(!pot) return;
  finderState.target = pot;
  targetSearchInput.value = '';
  potPickerResults.innerHTML = '';
  document.getElementById('selectedTarget').innerHTML = `
    <div class="selected-target-card">
      <div class="result-sigil" style="width:36px;height:36px;">${sigilSVG(pot.stats,{stroke:'#c79a4b'})}</div>
      <div><strong>${escapeHtml(pot.name)}</strong> ${rarityChip(pot.rarity)}</div>
    </div>`;
  document.getElementById('findBtn').disabled = false;
});

document.getElementById('findBtn').addEventListener('click', ()=>{
  if(!finderState.target) return;
  const count = Math.max(2, Math.min(6, parseInt(document.getElementById('ingCountInput').value) || 2));
  const techniqueKey = document.getElementById('finderTechniqueSelect').value;
  const maxAttempts = parseInt(document.getElementById('maxAttemptsSelect').value);
  const pool = availableIngredientsForTarget(finderState.target);

  const progressWrap = document.getElementById('searchProgress');
  const progressFill = document.getElementById('progressFill');
  const progressLabel = document.getElementById('progressLabel');
  const resultEl = document.getElementById('finderResult');
  const findBtn = document.getElementById('findBtn');

  progressWrap.classList.remove('hidden');
  findBtn.disabled = true;
  resultEl.innerHTML = `<div class="empty-note"><p>Searching…</p></div>`;

  const CHUNK = 800;
  let attempt = 0;
  let found = null;

  function step(){
    const end = Math.min(maxAttempts, attempt + CHUNK);
    for(; attempt < end; attempt++){
      const recipe = randomRecipe(pool, count); // count is always >= 2 raw picks, matching the notebook's len(recipe)>1 check
      const { scored } = dictBrew(recipe, techniqueKey);
      if(scored.length && scored[0].pot.name === finderState.target.name){
        found = recipe;
        break;
      }
    }
    progressFill.style.width = `${Math.round(100*attempt/maxAttempts)}%`;
    progressLabel.textContent = `Attempt ${attempt.toLocaleString()} of ${maxAttempts.toLocaleString()}…`;

    if(found || attempt >= maxAttempts){
      progressWrap.classList.add('hidden');
      findBtn.disabled = false;
      renderFinderResult(found, finderState.target, attempt);
      return;
    }
    setTimeout(step, 0);
  }
  step();
});

function renderFinderResult(recipe, target, attempts){
  const resultEl = document.getElementById('finderResult');
  if(!recipe){
    resultEl.innerHTML = `
      <div class="recipe-not-found">
        <p>No recipe found after <strong>${attempts.toLocaleString()}</strong> attempts.</p>
        <p>Try a higher search effort, a different ingredient count, or a different technique.</p>
      </div>`;
    return;
  }
  resultEl.innerHTML = `
    <div class="recipe-found">
      <div class="result-header">
        <div class="result-sigil">${sigilSVG(target.stats,{stroke:'#6fae94', fill:'rgba(111,174,148,0.2)'})}</div>
        <div class="result-title"><h3>${escapeHtml(target.name)}</h3>${rarityChip(target.rarity)}</div>
      </div>
      <p class="match-label">Found in ${attempts.toLocaleString()} attempts.</p>
      <div class="r-ing-list">
        ${recipe.map(({item,qty})=>`
          <div class="r-ing-row"><span>${escapeHtml(item.name)}</span><span>${rarityChip(item.rarity)} ${qty>1?`× ${qty}`:''}</span></div>
        `).join('')}
      </div>
    </div>`;
}

/* ============================================================
   Catalogs (Ingredients / Potions)
   ============================================================ */
function buildCatalog({ data, gridId, searchId, filterId, kind }){
  const state = { query: '', rarity: null };
  const grid = document.getElementById(gridId);
  const searchInput = document.getElementById(searchId);
  const filterWrap = document.getElementById(filterId);

  const rarities = RARITY_ORDER.filter(r => data.some(d=>d.rarity===r));
  filterWrap.innerHTML = rarities.map(r=>`<button class="filter-chip" data-r="${r}">${r}</button>`).join('');
  filterWrap.addEventListener('click', (e)=>{
    const chip = e.target.closest('.filter-chip');
    if(!chip) return;
    const r = chip.dataset.r;
    state.rarity = state.rarity === r ? null : r;
    filterWrap.querySelectorAll('.filter-chip').forEach(c=>c.classList.toggle('active', c.dataset.r === state.rarity));
    render();
  });

  searchInput.addEventListener('input', ()=>{ state.query = searchInput.value.trim().toLowerCase(); render(); });

  function render(){
    let items = data;
    if(state.rarity) items = items.filter(d=>d.rarity===state.rarity);
    if(state.query) items = items.filter(d=>d.name.toLowerCase().includes(state.query));
    grid.innerHTML = items.map(d => cardHTML(d, kind)).join('') || `<p class="empty-note">No ${kind}s match your search.</p>`;
  }

  render();
}

function cardHTML(item, kind){
  const desc = kind==='ingredient' ? item.description : item.effect;
  return `
    <div class="item-card" data-name="${escapeHtml(item.name)}" data-kind="${kind}">
      <div class="card-top">
        <div>
          <h4>${escapeHtml(item.name)}</h4>
          <div class="card-sub">${rarityChip(item.rarity)}${item.value ? ' · ' + escapeHtml(item.value) : ''}</div>
        </div>
        <div class="card-sigil">${sigilSVG(item.stats, {stroke: kind==='ingredient' ? '#6fae94' : '#9b7fce'})}</div>
      </div>
      ${desc ? `<p class="card-desc">${escapeHtml(desc)}</p>` : ''}
      ${kind==='potion' && item.consumption ? `<p class="card-desc" style="margin-top:4px;"><em>${escapeHtml(item.consumption)}</em></p>` : ''}
      <div class="card-detail">
        ${statTable(item.stats)}
      </div>
    </div>`;
}

document.getElementById('ingredientGrid').addEventListener('click', (e)=>{
  const card = e.target.closest('.item-card');
  if(card) card.classList.toggle('expanded');
});
document.getElementById('potionGrid').addEventListener('click', (e)=>{
  const card = e.target.closest('.item-card');
  if(card) card.classList.toggle('expanded');
});

buildCatalog({ data: INGREDIENTS, gridId:'ingredientGrid', searchId:'ingCatalogSearch', filterId:'ingRarityFilters', kind:'ingredient' });
buildCatalog({ data: POTIONS, gridId:'potionGrid', searchId:'potCatalogSearch', filterId:'potRarityFilters', kind:'potion' });

/* ============================================================
   Guide — technique list
   ============================================================ */
document.getElementById('guideTechniques').innerHTML = Object.values(TECHNIQUES).map(t=>`
  <div class="technique-entry"><span class="t-name">${t.label}:</span> ${t.hint}</div>
`).join('');
