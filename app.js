const $ = id => document.getElementById(id);
const esc = text => String(text).replace(/[&<>"']/g, c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const colors = {done:'#25a672',broken:'#e66770',progress:'#6297f3',matched:'#dfa940',unaddressed:'#fff',na:'#a9b2bf'};
const labels = {done:'Reviewed',broken:'Needs work',progress:'In progress',matched:'Matched',unaddressed:'Unaddressed',na:'Rocq-only (n/a)'};
const statusGuide = {
  done: {short:'Checked against Flocq', detail:'Green: the statement has recorded review evidence against pinned Flocq — the port’s review queue or ledger, or a Claude spot check. It is not a proof of universal equivalence.'},
  broken: {short:'Open issue or proof obligation', detail:'Red: a known issue, an open proof obligation, or a renamed Lean declaration whose statement differs from Flocq’s. This does not necessarily mean the implementation is incorrect.'},
  progress: {short:'Review under way', detail:'Blue: this declaration is part of the current review effort recorded in this snapshot.'},
  matched: {short:'Counterpart found; awaiting review', detail:'Yellow: a likely Lean counterpart has been found, by name, source anchor or the port’s rename classification, but it has not been marked reviewed in this map.'},
  unaddressed: {short:'No Lean counterpart yet', detail:'White: no Lean counterpart. The port’s classification lists these as missing; the note gives each one’s port plan.'},
  na: {short:'No Lean analogue by design', detail:'Grey: the port classifies it Rocq-only, with nothing to port: an SProp eliminator (Lean has no SProp) or a notation local to a Section (no compiled object). Only declarations with no Lean match by name were classified, so an eliminator or notation whose name a Lean declaration reuses keeps that match’s colour. Left out of progress ratios; in the roots view they are listed on each module’s strip.'}
};
const kinds = {prf:'theorem',def:'definition',abbrev:'notation / alias',ind:'inductive',constr:'constructor',rec:'record',proj:'projection',inst:'instance',scheme:'scheme'};
const phoneLayout=matchMedia('(max-width: 720px), (max-width: 950px) and (max-height: 500px)');
let data, nodeMap, moduleMap, moduleId='src/Core/Zaux.v', selectedId, mode=phoneLayout.matches?'declarations':'atlas', page=0, zoom=1, statusFilter=null, candidateIndex=0;
let visibleNodes=[], viewWidth=980, viewHeight=400, renderToken=0;
let atlasPositions=new Map(), cardPositions=new Map(), edgeMode='selected';
// Default view: definitions are roots. Theorems proven in Lean and spot-checked by Claude fold into what they use.
let scope='roots', rootEdgeList=[];
const pageSize=36, sourceCache=new Map();
const shown = n => scope==='all' || !n.hideInRoots;
// Rocq-only declarations are hidden in the roots graph but stay reachable on their module's strip.
const rocqOnly = n => n.status==='na';
const reachable = n => shown(n) || rocqOnly(n);
const unproved = n => n.role==='theorem' && !n.proven && !rocqOnly(n);
const naWhy = {'SProp eliminator':'Lean has no SProp universe, so Rocq’s generated SProp eliminator has no direct analogue; the Prop recursor covers it. Where the port defines a declaration under an eliminator’s name, that eliminator shows as matched instead.','section-local notation':'Rocq discards a notation declared inside a Section when the Section closes, so it leaves no compiled object; Lean writes its expansion inline. Section notations whose name a Lean declaration reuses show as matched to it instead.'};
const moduleNodes = m => m.nodes.map(id=>nodeMap.get(id)).filter(shown);
const activeEdges = () => scope==='roots' ? rootEdgeList : data.edges;
const foldCount = n => scope==='roots' ? (n.folded?.length||0) : 0;
function roleText(n){
  if(n.role!=='theorem')return n.roleBasis==='data term'?'definition (a data-returning theorem)':'definition';
  if(!n.proven)return 'unproved theorem';
  if(n.spotChecked)return 'proven, spot-checked theorem';
  return n.checked?'proven theorem, reviewed by the port but not yet spot-checked by Claude':'proven theorem, not yet checked';
}
const describe=(id,text)=>{$(id).textContent=text;$(id).title=text;};

async function load(){
  const response=await fetch('data.json');
  if(!response.ok) throw Error('The source snapshot could not be loaded.');
  data=await response.json();
  nodeMap=new Map(data.nodes.map(n=>[n.id,n])); moduleMap=new Map(data.modules.map(m=>[m.id,m]));
  // Compressed graph for the roots view: visible edges plus bridges across folded theorems.
  rootEdgeList=[...data.edges.filter(e=>!nodeMap.get(e.from).hideInRoots&&!nodeMap.get(e.to).hideInRoots),...data.roots.bridges.map(b=>({...b,bridge:true}))];
  $('snapshot').textContent='Snapshot · '+new Date(data.snapshot).toLocaleDateString('en-GB',{day:'numeric',month:'short',year:'numeric'});
  $('module-total').textContent=data.modules.length;
  $('source-pins').textContent=data.flocqPin.slice(0,8)+' / '+data.leanCommit.slice(0,8);
  const r=data.roots;
  $('about-stats').innerHTML=`<div><strong>${data.modules.length}</strong><span>source modules</span></div><div><strong>${data.nodes.length.toLocaleString()}</strong><span>declarations</span></div><div><strong>${data.edges.length.toLocaleString()}</strong><span>reference edges</span></div><div><strong>${r.roles.definition.toLocaleString()}</strong><span>definitions</span></div><div><strong>${r.roles.theorem.toLocaleString()}</strong><span>theorems</span></div><div><strong>${r.folded}</strong><span>folded in roots view</span></div><div><strong>${r.unprovedTheorems}</strong><span>unproved theorems</span></div><div><strong>${r.na}</strong><span>Rocq-only (n/a)</span></div>`;
  $('edge-provenance').textContent=data.dpdCoverage?`Solid lines come from dpdgraph, run on the same pinned Flocq source with Rocq 9.1. ${data.dpdCoverage.mapped.toLocaleString()} of ${data.dpdCoverage.nodes.toLocaleString()} dependency-graph objects map to source declarations; the rest are generated or ambiguous. Arrows point from dependency to consumer. Dashed lines show source order.`:'Solid lines are approximate .glob references; dashed lines show source order.';
  const mapped=data.openDebts.filter(d=>d.source).length,c=data.review.classification;
  $('about-pins').innerHTML=`Flocq <code>${esc(data.flocqPin.slice(0,12))}</code> · Lean snapshot <code>${esc(data.leanCommit.slice(0,12))}</code>. Source links point to those revisions. Green (checked) evidence comes from the port’s review queue (${data.review.queueChecked} entries), its review ledger (${data.review.ledgerEntries}) and Claude spot checks (${data.review.spotChecks}); only Claude-spot-checked theorems fold in the roots view. The port’s proof-debt manifest lists ${data.openDebts.length} open obligation${data.openDebts.length===1?'':'s'}; ${mapped} ${mapped===1?'is':'are'} shown in red on the Flocq law${mapped===1?'':'s'} ${mapped===1?'it refines':'they refine'}.`
    +(c?` The port’s classification of the ${c.entries} declarations with no named counterpart makes ${c.applied['renamed-match']} amber (renamed), ${c.applied['renamed-differs']} red (renamed, statement differs) and ${c.applied['not-applicable']} grey (Rocq-only), and keeps ${c.applied.missing} white (missing, with a port plan).`:'');
  renderNav();
  const hash=decodeURIComponent(location.hash.slice(1));
  const showcase=data.nodes.filter(n=>!n.hideInRoots).reduce((best,n)=>(n.folded?.length||0)>(best?.folded?.length||0)?n:best,null);
  const initial=nodeMap.get(hash) || showcase || data.nodes[0];
  selectNode(initial.id,false);
  setTimeout(fit,0);
}

function renderNav(){
  const query=$('search').value.trim().toLowerCase();
  $('nav-title').textContent=query?'SEARCH RESULTS':'SOURCE MODULES';
  let html='';
  if(query){
    const results=data.nodes.filter(n=>(n.name+' '+n.module).toLowerCase().includes(query));
    $('module-total').textContent=results.length;
    html=results.slice(0,100).map(n=>`<button class="module-button search-result ${n.id===selectedId?'active':''}" data-node="${esc(n.id)}"><i class="dot ${n.status}"></i><span class="result-content"><strong>${esc(n.name)}</strong><small>${esc(moduleMap.get(n.module).name)} · L${n.line}${!shown(n)?(rocqOnly(n)?' · Rocq-only':' · folded'):unproved(n)?' · unproved':''}</small></span></button>`).join('');
    if(!results.length) html='<p class="no-results">No declarations found. Try a shorter name or a module such as Ulp.</p>';
    if(results.length>100) html+='<p class="no-results">Showing the first 100 matches. Keep typing to narrow the list.</p>';
  }else{
    $('module-total').textContent=data.modules.length;
    let group='';
    for(const m of data.modules){
      const g=m.name.includes('/')?m.name.split('/')[0]:'Metadata';
      if(g!==group){ html+=`<div class="nav-group">${esc(g)}</div>`;group=g; }
      html+=`<button class="module-button ${m.id===moduleId?'active':''}" data-module="${esc(m.id)}"><span class="num">${String(m.rank+1).padStart(2,'0')}</span><span class="module-label">${esc(m.name.split('/').at(-1))}</span><small>${moduleNodes(m).length}</small></button>`;
    }
  }
  $('modules').innerHTML=html;
}
function renderLegend(){
  // Every declaration counts in both views, so the legend adds up to the whole library. In the roots
  // view folded theorems and Rocq-only declarations are on module strips, and the header's
  // shown + folded + Rocq-only split the same total.
  const counts=Object.fromEntries(Object.keys(labels).map(s=>[s,data.nodes.filter(n=>n.status===s).length]));
  $('legend').innerHTML=Object.keys(labels).filter(s=>counts[s]||s===statusFilter).map(s=>`<button class="legend-button ${s===statusFilter?'chosen':''}" data-status="${s}" aria-describedby="guide-${s}" aria-label="Filter to ${labels[s].toLowerCase()}, ${counts[s]} declarations"><span class="legend-label"><i class="dot ${s}"></i>${labels[s]} <span>${counts[s]}</span></span><span class="legend-description">${statusGuide[s].short}</span><span class="legend-tooltip" id="guide-${s}" role="tooltip">${statusGuide[s].detail}</span></button>`).join('');
  $('legend-caveat').innerHTML=scope==='roots'
    ?`<span class="long">Theorems proven in Lean and spot-checked by Claude fold into what they use (<b class="badge-key">+n</b>). Click a color to filter.</span><span class="short">Proven, spot-checked theorems fold into <b class="badge-key">+n</b> badges.</span>`
    :'<span class="long">Colors are review status, not correctness certificates. Click a color to filter.</span><span class="short">Colors are review status, not proofs.</span>';
  $('bridge-key').hidden=scope!=='roots';
}

function nodePosition(index){if(phoneLayout.matches)return{x:14,y:18+index*82,w:332,h:65};const row=Math.floor(index/3),col=row%2?2-index%3:index%3;return{x:35+col*315,y:35+row*106,w:278,h:65};}
function pathBetween(a,b,order=false){
  if(order && a.y===b.y){ const forward=b.x>a.x; return `M${a.x+(forward?a.w:0)} ${a.y+a.h/2}H${b.x+(forward?0:b.w)}`; }
  const ax=a.x+a.w/2, ay=a.y+a.h, bx=b.x+b.w/2, by=b.y;
  const delta=Math.max(20,(by-ay)/2);
  return `M${ax} ${ay} C${ax} ${ay+delta},${bx} ${by-delta},${bx} ${by}`;
}
function graphDefs(){return `<defs><marker id="arrow" markerWidth="6" markerHeight="6" refX="5" refY="3" orient="auto"><path d="M0 0L6 3L0 6" fill="none" stroke="#91a5c1" stroke-width="1"/></marker></defs>`;}
function bridgeTitle(e){return e.bridge?`<title>Through folded ${esc(e.via.map(id=>nodeMap.get(id).name).join(', '))}</title>`:'';}
function renderAtlas(){
  const columns=4, cardWidth=940, gap=40, cellWidth=112, cellHeight=27;
  const panels=[];atlasPositions=new Map();let top=35;
  for(let row=0;row<data.modules.length;row+=columns){
    const group=data.modules.slice(row,row+columns);let rowHeight=0;
    group.forEach((m,col)=>{
      const list=moduleNodes(m);
      const x=35+col*(cardWidth+gap),h=95+Math.ceil(list.length/8)*cellHeight;
      panels.push({m,x,y:top,w:cardWidth,h,count:list.length});rowHeight=Math.max(rowHeight,h);
      list.forEach((n,index)=>{const r=Math.floor(index/8),c=r%2?7-index%8:index%8;
        atlasPositions.set(n.id,{x:x+22+c*cellWidth,y:top+65+r*cellHeight,w:104,h:21});});
    });top+=rowHeight+gap;
  }
  const edges=activeEdges(),selected=nodeMap.get(selectedId);
  const hosts=new Set(selected&&!shown(selected)?selected.foldedInto:[]);
  let html=graphDefs();
  for(const p of panels){
    const folded=(scope==='roots'&&p.m.folded?` · +${p.m.folded} folded`:'')+(scope==='roots'&&p.m.na?` · ${p.m.na} n/a`:'');
    html+=`<g class="atlas-panel"><rect x="${p.x}" y="${p.y}" width="${p.w}" height="${p.h}" rx="12"/><text class="atlas-module-title" x="${p.x+24}" y="${p.y+32}" data-module="${esc(p.m.id)}" role="button" tabindex="0">${String(p.m.rank+1).padStart(2,'0')} · ${esc(p.m.name)}</text><text class="atlas-module-count" x="${p.x+p.w-24}" y="${p.y+32}">${p.count} ${scope==='roots'?'shown':'declarations'}${folded}</text></g>`;
  }
  if(edgeMode!=='none'){
    for(const edge of edges){
      const related=edge.from===selectedId||edge.to===selectedId;
      if(edgeMode==='selected'&&!related)continue;
      if(statusFilter&&nodeMap.get(edge.from).status!==statusFilter&&nodeMap.get(edge.to).status!==statusFilter)continue;
      const a=atlasPositions.get(edge.from),b=atlasPositions.get(edge.to);if(!a||!b)continue;
      html+=`<path class="atlas-edge ${related?'related':''} ${edge.bridge?'bridge':''}" d="${pathBetween(a,b)}" marker-end="url(#arrow)">${bridgeTitle(edge)}</path>`;
    }
  }
  const neighbors=new Set(edges.filter(e=>e.from===selectedId||e.to===selectedId).flatMap(e=>[e.from,e.to]));
  for(const n of data.nodes){
    const p=atlasPositions.get(n.id);if(!p)continue;
    const dim=statusFilter&&n.status!==statusFilter,badge=foldCount(n),limit=badge?(badge>99?11:13):17;
    const classes=[n.status,'role-'+n.role,unproved(n)?'unproved':'',n.id===selectedId?'selected':'',neighbors.has(n.id)?'neighbor':'',hosts.has(n.id)?'host':'',dim?'dimmed':''].filter(Boolean).join(' ');
    html+=`<g class="atlas-node ${classes}" role="button" tabindex="${dim?-1:0}" data-node="${esc(n.id)}" aria-label="${esc(n.name)}, ${roleText(n)}, ${labels[n.status]}${badge?`, ${badge} spot-checked theorems folded here`:''}"><title>${esc(moduleMap.get(n.module).name)} / ${esc(n.name)} · ${roleText(n)} · ${labels[n.status]} · L${n.line}${badge?` · +${badge} proven, spot-checked theorems folded here`:''}</title><rect x="${p.x}" y="${p.y}" width="${p.w}" height="${p.h}" rx="${n.role==='theorem'?10:2}" fill="${colors[n.status]}"/><text x="${p.x+5}" y="${p.y+14}">${esc(n.name.length>limit?n.name.slice(0,limit-1)+'…':n.name)}</text>`;
    if(badge){const w=badge>99?24:badge>9?19:15;html+=`<g class="fold-badge"><rect x="${p.x+p.w-w-3}" y="${p.y+4}" width="${w}" height="13" rx="6.5"/><text x="${p.x+p.w-3-w/2}" y="${p.y+13.5}" text-anchor="middle">+${badge}</text></g>`;}
    html+='</g>';
  }
  const total=[...atlasPositions.keys()].length;
  viewWidth=columns*(cardWidth+gap)+30;viewHeight=top;
  $('module-rank').textContent='ALL';$('module-name').textContent='The whole Flocq library';
  describe('module-description',`${total.toLocaleString()} ${scope==='roots'?`shown · ${data.roots.folded} folded · ${data.roots.na} Rocq-only`:'declarations'} · ${edges.length.toLocaleString()} dependencies · ${data.modules.length} modules in coqdep order`);
  // The roots atlas has no cell for a Rocq-only declaration: say where a filter to them leads.
  const nothingHere=statusFilter&&!data.nodes.some(n=>shown(n)&&n.status===statusFilter);
  $('graph-caption').textContent=nothingHere?`${labels[statusFilter]} declarations are hidden in this view · they are listed on each module’s strip`:selected&&!shown(selected)?(rocqOnly(selected)?`${selected.name} is Rocq-only (n/a) · listed on its module’s strip`:`${selected.name} is folded into ${selected.foldedInto.length?selected.foldedInto.map(id=>nodeMap.get(id).name).join(', '):'no visible declaration (see its module)'} · Locate to zoom there`):'Scroll to explore · Ctrl/⌘ + wheel to zoom · Locate to read a node';
  $('page-label').textContent='All '+total.toLocaleString();
  $('page-prev').disabled=true;$('page-next').disabled=true;
  return html;
}
// A module's strip, after its last page, so no hidden declaration is unreachable: its folded
// theorems, then its Rocq-only (n/a) declarations under their own heading. A status filter
// keeps only the matching group.
const shelfGroups=m=>{
  const hidden=m.nodes.map(id=>nodeMap.get(id)).filter(n=>n.hideInRoots);
  return {folded:!statusFilter||statusFilter==='done'?hidden.filter(n=>!rocqOnly(n)):[],na:!statusFilter||statusFilter==='na'?hidden.filter(rocqOnly):[]};
};
function renderShelf(m,top){
  const {folded,na}=shelfGroups(m);
  const phone=phoneLayout.matches,columns=phone?1:3,width=phone?332:278,step=phone?340:315,left=phone?14:35,chip=phone?40:26,row=phone?48:34;
  let html='',y=top;
  const chips=(list,chipHtml)=>{list.forEach((n,i)=>{const x=left+(i%columns)*step,cy=y+50+Math.floor(i/columns)*row;cardPositions.set(n.id,{x,y:cy,w:width,h:chip});html+=chipHtml(n,x,cy);});y+=60+Math.ceil(list.length/columns)*row;};
  if(folded.length){
    const unhosted=folded.filter(n=>!n.foldedInto.length).length;
    html+=`<text class="fold-shelf-title" x="${left}" y="${y+18}">Folded here · ${folded.length} proven, spot-checked theorem${folded.length===1?'':'s'}</text><text class="fold-shelf-note" x="${left}" y="${y+36}">${phone?'Hidden in the roots view.':'Hidden in the roots view; each also appears as a +n badge on what it depends on.'}${unhosted?` ${unhosted} depend on no visible declaration.`:''}</text>`;
    chips(folded,(n,x,cy)=>{
      const label=n.name.length>34?n.name.slice(0,33)+'…':n.name,hosts=n.foldedInto.length?n.foldedInto.map(id=>nodeMap.get(id).name).join(', '):'no visible dependency';
      return `<g class="fold-chip ${n.id===selectedId?'selected':''}" role="button" tabindex="0" data-node="${esc(n.id)}" aria-label="${esc(n.name)}, folded into ${esc(hosts)}"><title>${esc(n.name)} · folded into ${esc(hosts)}</title><rect x="${x}" y="${cy}" width="${width}" height="${chip}" rx="${chip/2}"/><text x="${x+14}" y="${cy+chip/2+4}">${esc(label)}</text></g>`;
    });
  }
  if(na.length){
    if(folded.length)y+=6;
    html+=`<text class="fold-shelf-title na" x="${left}" y="${y+18}">Rocq-only (n/a) · ${na.length}${phone?'':` declaration${na.length===1?'':'s'}`} with no Lean analogue</text><text class="fold-shelf-note na" x="${left}" y="${y+36}">${phone?'SProp eliminators and section notations.':'SProp eliminators and section-local notations. Hidden in the roots view and left out of progress ratios.'}</text>`;
    chips(na,(n,x,cy)=>{
      const tag=n.naReason==='SProp eliminator'?'SPROP':'NOTATION',label=n.name.length>24?n.name.slice(0,23)+'…':n.name;
      return `<g class="fold-chip na ${n.id===selectedId?'selected':''}" role="button" tabindex="0" data-node="${esc(n.id)}" aria-label="${esc(n.name)}, Rocq-only: ${esc(n.naReason)}"><title>${esc(n.name)} · Rocq-only: ${esc(n.naReason)}</title><rect x="${x}" y="${cy}" width="${width}" height="${chip}" rx="${chip/2}"/><text x="${x+14}" y="${cy+chip/2+4}">${esc(label)}</text><text class="chip-reason" x="${x+width-14}" y="${cy+chip/2+3.5}" text-anchor="end">${tag}</text></g>`;
    });
  }
  return {html,height:y-top};
}
function renderGraph(){
  const m=moduleMap.get(moduleId);
  $('module-rank').textContent=mode==='modules'?String(data.modules.length):String(m.rank+1).padStart(2,'0');
  $('module-name').textContent=mode==='modules'?'The Flocq dependency map':m.name.replaceAll('/',' / ');
  const listed=moduleNodes(m);
  describe('module-description',mode==='modules'?'Imports first. Then work down each file.':`${listed.length} ${scope==='roots'?`shown${m.folded?` · ${m.folded} folded`:''}${m.na?` · ${m.na} Rocq-only`:''}`:'declarations'} · source order · ${m.dependencies.length} direct module imports`);
  $('declarations-view').classList.toggle('active',mode==='declarations');$('modules-view').classList.toggle('active',mode==='modules');
  $('atlas-view').classList.toggle('active',mode==='atlas');
  $('page-prev').hidden=mode!=='declarations';$('page-next').hidden=mode!=='declarations';
  $('edge-mode').hidden=mode==='modules';
  renderLegend();
  $('reset-filter').hidden=!statusFilter;
  let html=graphDefs();cardPositions=new Map();
  if(mode==='atlas'){
    html=renderAtlas();
  }else if(mode==='modules'){
    const positions=new Map(data.modules.map((mod,index)=>[mod.id,{x:30+(index%5)*205,y:30+Math.floor(index/5)*112,w:178,h:72}]));
    for(const mod of data.modules)for(const dep of mod.dependencies){
      const a=positions.get(dep),b=positions.get(mod.id);if(!a)continue;
      html+=`<path class="module-edge" d="${pathBetween(a,b)}" marker-end="url(#arrow)"/>`;
    }
    for(const mod of data.modules){
      // Progress bars: Rocq-only declarations are not porting work, so they leave the denominator.
      const p=positions.get(mod.id),list=moduleNodes(mod),portable=list.filter(n=>!rocqOnly(n)),counts=Object.fromEntries(Object.keys(labels).map(s=>[s,portable.filter(n=>n.status===s).length]));
      let sx=0,bars='';
      for(const s of Object.keys(labels)){const w=(counts[s]/Math.max(1,portable.length))*150;if(w){bars+=`<rect x="${p.x+14+sx}" y="${p.y+59}" width="${w}" height="4" fill="${s==='unaddressed'?'#dce3ed':colors[s]}"/>`;sx+=w;}}
      const count=scope==='roots'?`${list.length} shown${mod.folded?` · +${mod.folded} folded`:''}`:`${list.length} declarations`;
      html+=`<g class="node module-node ${mod.id===moduleId?'selected':''}" role="button" tabindex="0" data-module="${esc(mod.id)}" aria-label="Open module ${esc(mod.name)}"><title>${esc(mod.name)} · ${count}${mod.na?` · ${mod.na} Rocq-only (n/a), left out of the progress bar`:''}</title><rect class="node-box" x="${p.x}" y="${p.y}" width="${p.w}" height="${p.h}" rx="7"/><text x="${p.x+14}" y="${p.y+24}" class="node-title">${esc(mod.name.split('/').at(-1))}</text><text x="${p.x+14}" y="${p.y+43}" class="node-subtitle">${esc(mod.name.split('/')[0])} · ${count}</text><text x="${p.x+p.w-24}" y="${p.y+23}" class="node-number">${String(mod.rank+1).padStart(2,'0')}</text>${bars}</g>`;
    }
    viewWidth=1060;viewHeight=30+Math.ceil(data.modules.length/5)*112;
    $('graph-caption').textContent='Select a module to explore its declarations.';
    $('page-label').textContent=data.modules.length+' modules';$('page-prev').disabled=true;$('page-next').disabled=true;
  }else{
    const all=listed.filter(n=>!statusFilter||n.status===statusFilter);
    const shelf=scope==='roots'?shelfGroups(m):{folded:[],na:[]},withShelf=shelf.folded.length+shelf.na.length>0;
    const shelfText=[shelf.folded.length?`${shelf.folded.length} folded`:'',shelf.na.length?`${shelf.na.length} Rocq-only`:''].filter(Boolean).join(' and ');
    const pages=Math.max(1,Math.ceil(all.length/pageSize));page=Math.min(page,pages-1);
    visibleNodes=all.slice(page*pageSize,(page+1)*pageSize);
    const positions=new Map(visibleNodes.map((n,i)=>[n.id,nodePosition(i)]));
    visibleNodes.forEach((n,i)=>{cardPositions.set(n.id,positions.get(n.id));if(i){html+=`<path class="order-edge" d="${pathBetween(positions.get(visibleNodes[i-1].id),positions.get(n.id),true)}" marker-end="url(#arrow)"/>`;}});
    for(const e of activeEdges()){
      if(!positions.has(e.from)||!positions.has(e.to))continue;
      if(edgeMode==='none'||(edgeMode==='selected'&&e.from!==selectedId&&e.to!==selectedId))continue;
      html+=`<path class="reference-edge ${e.from===selectedId||e.to===selectedId?'related':''} ${e.bridge?'bridge':''}" d="${pathBetween(positions.get(e.from),positions.get(e.to))}" marker-end="url(#arrow)">${bridgeTitle(e)}</path>`;
    }
    const selected=nodeMap.get(selectedId),hosts=new Set(selected&&!shown(selected)?selected.foldedInto:[]);
    visibleNodes.forEach(n=>{
      const p=positions.get(n.id),badge=foldCount(n),max=badge?20:30,title=n.name.length>max?n.name.slice(0,max-2)+'…':n.name;
      const classes=[n.status,'role-'+n.role,unproved(n)?'unproved':'',n.id===selectedId?'selected':'',hosts.has(n.id)?'host':''].filter(Boolean).join(' ');
      html+=`<g class="node ${classes}" role="button" tabindex="0" data-node="${esc(n.id)}" aria-label="${esc(n.name)}, ${roleText(n)}, ${labels[n.status]}${badge?`, ${badge} spot-checked theorems folded here`:''}"><title>${esc(n.name)} · ${roleText(n)} · ${labels[n.status]} · line ${n.line}${badge?` · +${badge} proven, spot-checked theorems folded here`:''}</title><rect class="node-box" x="${p.x}" y="${p.y}" width="${p.w}" height="${p.h}" rx="${n.role==='theorem'?18:4}"/>`;
      if(n.role==='definition')html+=`<rect class="role-bar" x="${p.x}" y="${p.y+9}" width="3.5" height="${p.h-18}" rx="1.5"/>`;
      html+=`<circle cx="${p.x+15}" cy="${p.y+21}" r="3.8" fill="${colors[n.status]}" stroke="${n.status==='unaddressed'?'#a7b6cb':'none'}"/><text x="${p.x+28}" y="${p.y+25}" class="node-title">${esc(title)}</text><text x="${p.x+15}" y="${p.y+47}" class="node-subtitle">${esc(kinds[n.kind]||n.kind)}${n.roleBasis==='proof term'?' (proof)':n.roleBasis==='data term'?' (data)':''} · L${n.line}</text>`;
      if(unproved(n))html+=`<text x="${p.x+p.w-46}" y="${p.y+47}" class="unproved-tag" text-anchor="end">UNPROVED</text>`;
      else if(rocqOnly(n))html+=`<text x="${p.x+p.w-46}" y="${p.y+47}" class="na-tag" text-anchor="end">ROCQ-ONLY</text>`;
      if(badge){const label=`+${badge} folded`,w=label.length*6.2+14;html+=`<g class="card-badge"><rect x="${p.x+p.w-10-w}" y="${p.y+12}" width="${w}" height="17" rx="8.5"/><text x="${p.x+p.w-10-w/2}" y="${p.y+24.5}" text-anchor="middle">${label}</text></g>`;}
      html+=`<text x="${p.x+p.w-36}" y="${p.y+47}" class="node-number">${String(n.index+1).padStart(3,'0')}</text></g>`;
    });
    if(!visibleNodes.length&&!withShelf)html+='<text x="35" y="60" class="empty-graph">No declarations with this status in this module.</text>';
    let height=Math.max(180,phoneLayout.matches?visibleNodes.length*82+36:Math.ceil(visibleNodes.length/3)*106+50);
    if(withShelf&&page===pages-1){const strip=renderShelf(m,visibleNodes.length?height-10:30);html+=strip.html;height=(visibleNodes.length?height-10:30)+strip.height+20;}
    viewWidth=phoneLayout.matches?360:980;viewHeight=height;
    $('page-label').textContent=`${page+1} / ${pages}`;
    $('page-prev').disabled=page===0;$('page-next').disabled=page+1>=pages;
    $('graph-caption').textContent=`${all.length?`${page*pageSize+1}–${Math.min((page+1)*pageSize,all.length)} of ${all.length}`:'0'} declarations${withShelf?` · ${shelfText} ${all.length?'after the last page':'on the module strip'}`:''} · scroll to explore`;
  }
  const svg=$('graph');svg.innerHTML=html;svg.setAttribute('viewBox',`0 0 ${viewWidth} ${viewHeight}`);applyZoom();
}
function applyZoom(){const svg=$('graph');svg.style.width=(viewWidth*zoom)+'px';svg.style.height=(viewHeight*zoom)+'px';svg.style.minWidth='0';svg.classList.toggle('distant',mode==='atlas'&&zoom<.38);}
function fit(){zoom=Math.max(.08,Math.min(1.25,($('graph-wrap').clientWidth-10)/viewWidth));applyZoom();}
function changeZoom(next,cx=$('graph-wrap').clientWidth/2,cy=$('graph-wrap').clientHeight/2){
  const wrap=$('graph-wrap'),old=zoom,x=(wrap.scrollLeft+cx)/old,y=(wrap.scrollTop+cy)/old;
  zoom=Math.max(.08,Math.min(3,next));applyZoom();wrap.scrollTo({left:x*zoom-cx,top:y*zoom-cy,behavior:'instant'});
}
function locate(){
  if(mode==='modules'){mode='atlas';renderGraph();}
  const n=nodeMap.get(selectedId);
  // A folded theorem is located at the first declaration it was folded into.
  const p=mode==='atlas'?atlasPositions.get(selectedId)||atlasPositions.get(n?.foldedInto?.[0]):cardPositions.get(selectedId);
  if(!p)return;zoom=mode==='atlas'?1.1:1;applyZoom();
  $('graph-wrap').scrollTo({left:(p.x+p.w/2)*zoom-$('graph-wrap').clientWidth/2,top:(p.y+p.h/2)*zoom-$('graph-wrap').clientHeight/2,behavior:'instant'});
}
function setScope(next){
  if(next===scope)return;scope=next;
  document.querySelectorAll('button[data-scope]').forEach(b=>{const on=b.dataset.scope===scope;b.classList.toggle('active',on);b.setAttribute('aria-pressed',on);});
  renderNav();
  if(mode==='modules'||!nodeMap.get(selectedId)){renderGraph();if(selectedId)renderInspector();}
  else selectNode(selectedId,false);
  if(mode!=='declarations'){fit();$('graph-wrap').scrollTo(0,0);}
}

function selectModule(id){
  const m=moduleMap.get(id);if(!m)return;
  moduleId=id;mode='declarations';statusFilter=null;page=0;$('search').value='';
  const first=moduleNodes(m)[0]?.id||m.nodes[0];
  if(first)selectNode(first);else{
    selectedId=null;renderToken++;renderNav();renderGraph();
    $('selected-name').textContent=m.name+' — import-only module';$('selected-kind').textContent='';
    $('selected-status').textContent='Imports';$('selected-status').className='status-badge unaddressed';
    $('review-note').textContent='This module gathers imports and has no own declarations. Select one of its dependencies below.';
    $('coq-code').innerHTML='<div class="source-empty">No declarations in this module.</div>';
    $('lean-code').innerHTML='<div class="source-empty">The corresponding Lean aggregate imports the Core modules.</div>';
    $('candidate').innerHTML='<option>Import-only module</option>';$('candidate').disabled=true;
    $('coq-location').textContent=m.name+'.v';$('coq-link').href=`https://gitlab.inria.fr/flocq/flocq/-/blob/${data.flocqPin}/${m.id}`;
    $('lean-link').hidden=true;$('previous').disabled=true;$('next').disabled=true;
    $('relations').innerHTML='<span class="relation-label">IMPORTS</span>'+m.dependencies.map(id=>`<button data-module="${esc(id)}">${esc(moduleMap.get(id).name)}</button>`).join('');
  }
  $('graph-wrap').scrollTo(0,0);fit();
}
function selectNode(id,updateHash=true){
  const n=nodeMap.get(id);if(!n)return;
  const oldModule=moduleId; selectedId=id;moduleId=n.module;candidateIndex=0;
  if(statusFilter&&n.status!==statusFilter)statusFilter=null;
  const all=moduleNodes(moduleMap.get(moduleId)).filter(n=>!statusFilter||n.status===statusFilter);
  // Folded theorems and Rocq-only declarations sit on the strip after the module's last page.
  const at=shown(n)?all.findIndex(n=>n.id===id):Math.max(0,all.length-1);
  const nextPage=Math.floor(at/pageSize);
  // A hidden Rocq-only declaration has no atlas cell and no host: open its module's strip instead.
  if(mode==='atlas'&&!shown(n)&&rocqOnly(n))mode='declarations';
  const changed=oldModule!==moduleId||nextPage!==page;page=nextPage;if(mode!=='atlas')mode='declarations';
  if(updateHash)history.replaceState(null,'','#'+encodeURIComponent(id));
  renderNav();renderGraph();renderInspector();
  if(changed&&mode!=='atlas')$('graph-wrap').scrollTo(0,0);
  if(!shown(n)&&mode==='declarations')locate();
  if(document.body.classList.contains('graph-expanded'))$('expand').textContent='Read '+n.name+' ↙';
}
function syntax(line){
  const tokens=/(--.*|\(\*.*|\/\-.*|"(?:[^"\\]|\\.)*"|\b(?:Definition|Fixpoint|Lemma|Theorem|Proof|Qed|Defined|forall|exists|fun|match|with|end|if|then|else|let|in|Prop|Type|Set|Record|Inductive|Notation|Require|Import|From|Section|Variable|Context|by|def|theorem|lemma|noncomputable|private|opaque|axiom|structure|inductive|namespace|abbrev|instance|where|have|show|exact|intro|intros|apply|rw|simp|rfl|sorry)\b|\b\d+\b)/g;
  let result='',last=0;
  for(const m of line.matchAll(tokens)){result+=esc(line.slice(last,m.index));const t=m[0];const cl=/^(--|\(\*|\/\-)/.test(t)?'comment':t.startsWith('"')?'string':/^\d/.test(t)?'lit':'kw';result+=`<span class="${cl}">${esc(t)}</span>`;last=m.index+t.length;}
  return result+esc(line.slice(last));
}
async function source(kind,path){
  const key=kind+'/'+path;
  if(!sourceCache.has(key)) sourceCache.set(key,fetch('sources/'+key).then(r=>{if(!r.ok)throw Error('Source unavailable');return r.text();}));
  return sourceCache.get(key);
}
function codeHtml(text,start,end){
  const lines=text.split('\n'),stop=Math.min(lines.length,end,start+499);
  let html=lines.slice(start-1,stop).map((line,i)=>`<div class="code-line"><span class="line-number">${start+i}</span><span class="line-code">${syntax(line)||' '}</span></div>`).join('');
  if(end>stop)html+='<div class="source-empty">Excerpt capped at 500 lines. Open the source link for the remainder.</div>';
  return html;
}
function stepIds(n){return moduleMap.get(n.module).nodes.filter(id=>id===n.id||shown(nodeMap.get(id)));}
// Evidence behind green and behind folding, one flag per source.
const evidenceLabels={'Claude spot check':'Claude spot check','FloatSpec review queue':'port review queue','FloatSpec review ledger':'port review ledger'};
function flags(n){
  let html='';
  if(n.role==='theorem')html+=n.proven?'<span class="flag ok">proven</span>':'<span class="flag bad">unproved</span>';
  for(const by of new Set((n.checks||[]).map(c=>c.by)))html+=`<span class="flag ${by==='Claude spot check'?'ok':'review'}" title="Checked against pinned Flocq by ${esc(evidenceLabels[by]||by)}">${esc(evidenceLabels[by]||by)}</span>`;
  if(rocqOnly(n))html+=`<span class="flag na" title="${esc((n.naSection?`Declared inside Section ${n.naSection}. `:'')+(naWhy[n.naReason]||''))}">n/a · ${esc(n.naReason)}</span>`;
  else if(n.classification==='renamed-match')html+='<span class="flag" title="Lean counterpart under another name, per the port’s 2026-09-22 classification">renamed counterpart</span>';
  else if(n.classification==='renamed-differs')html+='<span class="flag bad" title="The renamed Lean declaration states something different">statement differs</span>';
  else if(n.classification==='missing')html+=`<span class="flag" title="Missing from the Lean port; the note gives the port plan">missing${n.portDifficulty&&n.portDifficulty!=='n/a'?' · '+esc(n.portDifficulty):''}</span>`;
  if(n.hideInRoots)html+=rocqOnly(n)?'<span class="flag fold">hidden in roots view</span>':'<span class="flag fold">folded in roots view</span>';
  else if(n.role==='theorem'&&n.proven&&n.checked&&!n.spotChecked)html+='<span class="flag">awaiting Claude spot check</span>';
  return html;
}
async function renderInspector(){
  const n=nodeMap.get(selectedId),token=++renderToken;
  if(!n)return;
  $('selected-name').textContent=n.name;
  $('selected-kind').innerHTML=esc(kinds[n.kind]||n.kind)+(n.roleBasis==='proof term'?' <span class="kind-note">(a proof, counted as a theorem)</span>':n.roleBasis==='data term'?' <span class="kind-note">(returns data, counted as a definition)</span>':'')+flags(n);
  $('selected-status').className='status-badge '+n.status;$('selected-status').textContent=labels[n.status];
  let note=n.note;
  if(n.hideInRoots&&rocqOnly(n))note+=' In Definitions (roots) it is hidden and listed under Rocq-only (n/a) on its module’s strip.';
  else if(n.hideInRoots)note+=n.foldedInto.length?` In Definitions (roots) this theorem is folded into ${n.foldedInto.map(id=>nodeMap.get(id).name).join(', ')}.`:' In Definitions (roots) it depends on no other visible Flocq declaration, so it is listed on its module’s folded shelf.';
  else if(n.folded?.length)note+=` ${n.folded.length} proven, spot-checked theorem${n.folded.length===1?' is':'s are'} folded into this declaration in the roots view.`;
  $('review-note').textContent=note;
  $('coq-location').textContent=moduleMap.get(n.module).name+'.v:'+n.line;
  $('coq-link').href=`https://gitlab.inria.fr/flocq/flocq/-/blob/${data.flocqPin}/${n.module}#L${n.line}`;
  const candidates=[...n.candidates,...n.related.map(c=>({...c,match:c.match||'related open obligation'}))];
  $('candidate').innerHTML=candidates.length?candidates.map((c,i)=>`<option value="${i}">${esc(c.name)} · ${esc(c.path.split('/').slice(-2).join('/'))} · ${esc(c.match)}</option>`).join(''):'<option>No counterpart found</option>';
  $('candidate').value=String(candidateIndex);$('candidate').disabled=!candidates.length;
  const ids=stepIds(n),index=ids.indexOf(n.id);
  $('previous').disabled=index===0;$('next').disabled=index===ids.length-1;
  renderRelations(n);
  $('coq-code').innerHTML='<div class="source-empty">Loading Coq source…</div>';
  $('lean-code').innerHTML='<div class="source-empty">Loading Lean source…</div>';
  try{
    const coq=await source('coq',n.module);if(token!==renderToken)return;
    $('coq-code').innerHTML=codeHtml(coq,n.line,n.end);$('coq-code').scrollTo(0,0);
  }catch{if(token===renderToken)$('coq-code').innerHTML='<div class="source-empty">Could not load this source. Use the pinned source link.</div>';}
  const c=candidates[candidateIndex];
  if(!c){
    $('lean-code').innerHTML=rocqOnly(n)?`<div class="source-empty"><strong>Not applicable to Lean · ${esc(n.naReason)}</strong>${n.naSection?`Declared inside Section <code>${esc(n.naSection)}</code>. `:''}${esc(naWhy[n.naReason]||'')}</div>`
      :n.classification==='missing'?'<div class="source-empty"><strong>Missing from the Lean port</strong>The port’s classification lists this declaration as missing. The note above gives the port plan.</div>'
      :'<div class="source-empty"><strong>No Lean match found</strong>This may be unported, renamed, or handled by different proof infrastructure. White means “not matched in this map,” not a confirmed missing implementation.</div>';
    $('lean-link').hidden=true;return;
  }
  $('lean-link').hidden=false;$('lean-link').href=`https://github.com/alok/FloatSpec/blob/${data.leanCommit}/${c.path}#L${c.line}`;
  try{const lean=await source('lean',c.path);if(token!==renderToken)return;$('lean-code').innerHTML=codeHtml(lean,c.line,c.end);$('lean-code').scrollTo(0,0);}catch{if(token===renderToken)$('lean-code').innerHTML='<div class="source-empty">Could not load this source. Use the repository link.</div>';}
}
function renderRelations(n){
  // Folded theorems keep their full edges; visible nodes use the current view's edges.
  const edges=scope==='roots'&&!n.hideInRoots?rootEdgeList:data.edges;
  const button=(id,extra='',title='')=>{const r=nodeMap.get(id);return `<button data-node="${esc(r.id)}" class="${extra}" title="${esc(title||moduleMap.get(r.module).name)}">${esc(r.name)}</button>`;};
  const via=e=>e.bridge?'Through folded '+e.via.map(id=>nodeMap.get(id).name).join(', '):'';
  const dependencies=edges.filter(e=>e.to===n.id),consumers=edges.filter(e=>e.from===n.id);
  let html='';
  if(n.folded?.length)html+=`<span class="relation-label">FOLDED HERE (${n.folded.length} SPOT-CHECKED THEOREM${n.folded.length===1?'':'S'})</span>`+n.folded.map(id=>button(id,'folded-item')).join('');
  if(n.hideInRoots&&rocqOnly(n))html+=`<span class="relation-label">ROCQ-ONLY (N/A)</span><span>${esc(n.naReason)} · listed on its module’s strip</span>`;
  else if(n.hideInRoots)html+=n.foldedInto.length?`<span class="relation-label">FOLDED INTO (${n.foldedInto.length})</span>`+n.foldedInto.map(id=>button(id,'host-item')).join(''):'<span class="relation-label">FOLDED INTO</span><span>no visible declaration · listed on its module’s shelf</span>';
  if(dependencies.length)html+='<span class="relation-label">USES ('+dependencies.length+')</span>'+dependencies.map(e=>button(e.from,e.bridge?'bridge':'',via(e))).join('');
  if(consumers.length)html+='<span class="relation-label">USED BY ('+consumers.length+')</span>'+consumers.map(e=>button(e.to,e.bridge?'bridge':'',via(e))).join('');
  $('relations').innerHTML=html||'<span>No internal reference edges recorded for this declaration.</span>';
}
function step(delta){const n=nodeMap.get(selectedId);if(!n)return;const ids=stepIds(n),next=ids[ids.indexOf(n.id)+delta];if(next)selectNode(next);}
document.addEventListener('click',event=>{
  const sourceView=event.target.closest('button[data-source-view]');if(sourceView){document.body.dataset.sourceView=sourceView.dataset.sourceView;document.querySelectorAll('button[data-source-view]').forEach(b=>b.setAttribute('aria-pressed',b===sourceView));return;}
  const scopeButton=event.target.closest('button[data-scope]');if(scopeButton){setScope(scopeButton.dataset.scope);return;}
  if(event.target.closest('[data-open-about]')){$('about-dialog').showModal();return;}
  const node=event.target.closest('[data-node]');if(node){selectNode(node.dataset.node);if(node.closest('#modules')&&mode==='atlas')locate();if(phoneLayout.matches&&!document.body.classList.contains('graph-expanded'))document.querySelector('.inspector').scrollIntoView({block:'start'});return;}
  const mod=event.target.closest('[data-module]');if(mod){selectModule(mod.dataset.module);return;}
  const status=event.target.closest('[data-status]');if(status){statusFilter=statusFilter===status.dataset.status?null:status.dataset.status;page=0;
    // The roots atlas has no cell for a hidden Rocq-only declaration: filtering to its status while it
    // is selected reselects it, which opens its module's strip.
    const sel=nodeMap.get(selectedId);
    if(mode==='atlas'&&statusFilter&&(sel?.status!==statusFilter||(!shown(sel)&&rocqOnly(sel)))){
      const first=sel?.status===statusFilter?sel:data.nodes.find(n=>n.status===statusFilter&&reachable(n));if(first){selectNode(first.id);locate();return;}
    }
    if(mode!=='atlas'&&statusFilter&&!moduleMap.get(moduleId).nodes.some(id=>{const n=nodeMap.get(id);return n.status===statusFilter&&reachable(n);})){
      const first=data.nodes.find(n=>n.status===statusFilter&&reachable(n));if(first)selectNode(first.id);
    }renderGraph();$('graph-wrap').scrollTo(0,0);}
});
document.addEventListener('keydown',event=>{
  if((event.key==='Enter'||event.key===' ')&&event.target.matches('g[role="button"]')){event.preventDefault();event.target.dispatchEvent(new MouseEvent('click',{bubbles:true}));}
  if(event.key==='/'&&!['INPUT','SELECT','TEXTAREA'].includes(document.activeElement.tagName)){event.preventDefault();$('search').focus();}
  if(event.altKey&&event.key==='ArrowRight'){event.preventDefault();step(1);}if(event.altKey&&event.key==='ArrowLeft'){event.preventDefault();step(-1);}
});
$('search').addEventListener('input',renderNav);
document.body.dataset.sourceView='coq';
$('back-to-map').onclick=()=>document.querySelector('.map-section').scrollIntoView({block:'start'});
phoneLayout.addEventListener('change',()=>{if(data){renderGraph();fit();}});
window.addEventListener('resize',()=>{if(data)fit();});
$('candidate').addEventListener('change',e=>{candidateIndex=+e.target.value;renderInspector();});
$('atlas-view').onclick=()=>{mode='atlas';renderGraph();fit();$('graph-wrap').scrollTo(0,0);};
$('modules-view').onclick=()=>{mode='modules';renderGraph();fit();$('graph-wrap').scrollTo(0,0);};
$('declarations-view').onclick=()=>{mode='declarations';renderGraph();fit();$('graph-wrap').scrollTo(0,0);};
$('reset-filter').onclick=()=>{statusFilter=null;page=0;renderGraph();};
$('previous').onclick=()=>step(-1);$('next').onclick=()=>step(1);
$('zoom-in').onclick=()=>changeZoom(zoom*1.5);$('zoom-out').onclick=()=>changeZoom(zoom/1.5);$('fit').onclick=fit;$('locate').onclick=locate;
$('edge-mode').onchange=e=>{edgeMode=e.target.value;renderGraph();};
$('expand').onclick=()=>{const expanded=document.body.classList.toggle('graph-expanded');$('expand').setAttribute('aria-pressed',expanded);$('expand').textContent=expanded?'Read sources ↙':'Expand ↗';fit();};
$('graph-wrap').addEventListener('wheel',e=>{if(!e.ctrlKey&&!e.metaKey)return;e.preventDefault();const r=$('graph-wrap').getBoundingClientRect();changeZoom(zoom*Math.exp(-e.deltaY*.003),e.clientX-r.left,e.clientY-r.top);},{passive:false});
$('graph').addEventListener('dblclick',e=>{if(e.target.closest('[data-node]'))locate();});
$('page-prev').onclick=()=>{page--;renderGraph();$('graph-wrap').scrollTo(0,0);};$('page-next').onclick=()=>{page++;renderGraph();$('graph-wrap').scrollTo(0,0);};
$('about').onclick=()=>$('about-dialog').showModal();$('close-about').onclick=()=>$('about-dialog').close();
$('about-dialog').onclick=e=>{if(e.target===$('about-dialog')){const r=e.target.getBoundingClientRect();if(e.clientX<r.left||e.clientX>r.right||e.clientY<r.top||e.clientY>r.bottom)e.target.close();}};
function setSplit(percent){percent=Math.max(30,Math.min(72,percent));document.querySelector('.map-section').style.height=percent+'%';$('splitter').setAttribute('aria-valuenow',Math.round(percent));}
$('splitter').onpointerdown=e=>{if(innerWidth<=720)return;e.preventDefault();$('splitter').setPointerCapture(e.pointerId);};
$('splitter').onpointermove=e=>{if(!$('splitter').hasPointerCapture(e.pointerId))return;const bounds=document.querySelector('main').getBoundingClientRect();setSplit((e.clientY-bounds.top)/bounds.height*100);};
$('splitter').onpointerup=e=>{if($('splitter').hasPointerCapture(e.pointerId))$('splitter').releasePointerCapture(e.pointerId);};
$('splitter').onkeydown=e=>{if(e.key==='ArrowUp'||e.key==='ArrowDown'){e.preventDefault();setSplit(+$('splitter').getAttribute('aria-valuenow')+(e.key==='ArrowUp'?-5:5));}};
window.addEventListener('hashchange',()=>{const id=decodeURIComponent(location.hash.slice(1));if(nodeMap?.has(id))selectNode(id,false);});
load().catch(error=>{$('graph-wrap').innerHTML=`<div class="error-banner">${esc(error.message)} Reload the page to try again.</div>`;console.error(error);});
