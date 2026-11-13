import json, math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
OUT='figures/'
plt.rcParams.update({'font.family':'serif','font.size':10,'mathtext.fontset':'cm'})

# 1. reduction diagram (pseudo-3D boxes)
fig,ax=plt.subplots(figsize=(8.2,3.0)); ax.set_xlim(0,10); ax.set_ylim(0,3.4); ax.axis('off')
def box3d(x,y,w,h,text,d=0.18):
    ax.add_patch(plt.Polygon([[x,y+h],[x+d,y+h+d],[x+w+d,y+h+d],[x+w,y+h]],closed=True,fc='0.82',ec='k',lw=0.8))
    ax.add_patch(plt.Polygon([[x+w,y],[x+w+d,y+d],[x+w+d,y+h+d],[x+w,y+h]],closed=True,fc='0.65',ec='k',lw=0.8))
    ax.add_patch(plt.Rectangle((x,y),w,h,fc='white',ec='k',lw=0.9))
    ax.text(x+w/2,y+h/2,text,ha='center',va='center',fontsize=9.5)
box3d(0.2,1.0,2.5,1.3,'squarefree ideal\n$I=\\mathfrak{p}_1\\cdots\\mathfrak{p}_k$\nof a Dedekind domain')
box3d(3.8,1.0,2.4,1.3,'norm multiset\n$\\mathcal{Q}=\\{q_1,\\dots,q_k\\}$\n$q_i=\\mathrm{N}(\\mathfrak{p}_i)$')
box3d(7.3,1.0,2.4,1.3,'arithmetic test\n$\\prod(q_i-1)\\mid\\prod q_i\\mp1$')
for (x1,x2,lab,yo) in [(2.9,3.75,'$\\mathcal{Q}(I)$',0.25),(6.4,7.25,'',0.25)]:
    ax.annotate('',xy=(x2,1.75),xytext=(x1,1.75),arrowprops=dict(arrowstyle='->',lw=1.1))
    ax.text((x1+x2)/2,1.75+yo,lab,ha='center',fontsize=8.5)
ax.annotate('',xy=(1.5,0.95),xytext=(5.0,0.95),arrowprops=dict(arrowstyle='->',lw=1.0,connectionstyle='arc3,rad=-0.35',ls='--'))
ax.text(3.25,0.15,'realization: every $\\mathcal{Q}$ comes from infinitely many number fields',ha='center',fontsize=8.5)
fig.savefig(OUT+'reduction.png',dpi=220,bbox_inches='tight'); plt.close(fig)

# 2. binary solutions 3D scatter
d={}
for f in ['bint.json','bint_5.json','bint_9.json']: d.update(json.load(open('../python/'+f)))
pts=[(int(t),len(S),F) for t in d for F,S in d[t]['sols'] if S]
fig=plt.figure(figsize=(6.4,4.6)); ax=fig.add_subplot(111,projection='3d')
for t,s,F in pts:
    ax.plot([t,t],[s,s],[0,F],color='0.55',lw=0.8)
    ax.scatter([t],[s],[F],color='k' if s>1 else 'white',edgecolor='k',s=26,depthshade=False)
ax.set_xlabel('$t$ (members equal to 2)'); ax.set_ylabel('$|S|$'); ax.set_zlabel('$F$')
ax.view_init(elev=22,azim=-58); ax.set_yticks([1,2,3,4])
for a in (ax.xaxis,ax.yaxis,ax.zaxis): a.pane.set_facecolor((1,1,1,0)); a.pane.set_edgecolor('0.6')
fig.savefig(OUT+'binary.png',dpi=220,bbox_inches='tight'); plt.close(fig)

# 3. one-prime inequality: log of both sides of (5.4), p=3,5,7
from sympy import totient
fig,ax=plt.subplots(figsize=(6.6,3.6))
styles={3:('k','-'),5:('0.35','--'),7:('0.6',':')}
for p in (3,5,7):
    cp=np.prod([1-p**-dd for dd in range(1,80)])
    Fs=np.arange(3,61)
    lhs=[max(int(totient(F))*math.log(p-1), math.log(cp)+int(totient(F))*math.log(p))-math.log(F) for F in Fs]
    rhs=[math.log2(p/(p-1))*math.log((p*p-1)*F/2) for F in Fs]
    c,ls=styles[p]
    ax.plot(Fs,np.array(lhs)-np.array(rhs),color=c,ls=ls,marker='o',ms=2.5,lw=1,label=f'$p={p}$')
ax.axhline(0,color='k',lw=0.6)
ax.set_ylim(-3,30); ax.set_xlabel('$F$'); ax.set_ylabel('log(left side) $-$ log(right side)')
ax.legend(frameon=False)
fig.savefig(OUT+'oneprime.png',dpi=220,bbox_inches='tight'); plt.close(fig)

# 4. search tree for uni k=5 eps=-1 (schematic, by depth, using a real traversal in python)
import itertools
def primepow(n):
    if n<2: return None
    for p in range(2,int(n**0.5)+2):
        if n%p==0:
            f=0;m=n
            while m%p==0: m//=p; f+=1
            return (p,f) if m==1 else None
    return (n,1)
K=5; nodes=[]; edges=[]; sols=[]
def rec(seq,A,B,M,parent):
    j=len(seq); m=K-j; C=M*B-A
    if C<=0: return
    lo=max(M*B//C+1, seq[-1] if seq else 3, 3)
    reach=lambda q: A*q**m > M*B*(q-1)**m
    if not reach(lo): return
    hi=lo
    while reach(2*hi): hi*=2
    a,b=hi,2*hi
    while b-a>1:
        c=(a+b)//2
        if reach(c): a=c
        else: b=c
    hi=a
    q=lo|1
    while q<=hi:
        pf=primepow(q)
        if pf and pf[0]%2==1:
            p,f=pf
            if M%p and all((q-1)%primepow(v)[0] and (v-1)%p for v in seq):
                me=len(nodes); nodes.append((j+1,q,M)); edges.append((parent,me))
                if m==2:
                    A2=A*q;B2=M*B*(q-1);D=B2-A2
                    if D>0 and (B2-1)%D==0:
                        x=(B2-1)//D; px=primepow(x)
                        if x>=q and px and all((x-1)%primepow(v)[0] for v in seq+[q]) and all((v-1)%px[0] for v in seq+[q]) and M%px[0]:
                            sols.append(me)
                else: rec(seq+[q],A*q,B*(q-1),M,me)
        q+=2
for M in range(2,int(1.5**K)+2):
    me=len(nodes); nodes.append((0,0,M)); rec([],1,1,M,me)
# layout: x by order of DFS leaves
depth=[n[0] for n in nodes]
fig=plt.figure(figsize=(7.6,4.3)); ax=fig.add_subplot(111,projection='3d')
xs={}; cnt=[0]
children={}
for a,b in edges: children.setdefault(a,[]).append(b)
def place(v):
    ch=children.get(v,[])
    if not ch: xs[v]=cnt[0]; cnt[0]+=1; return xs[v]
    xs[v]=np.mean([place(c) for c in ch]); return xs[v]
roots=[i for i,n in enumerate(nodes) if n[0]==0]
for r in roots: place(r)
for a,b in edges:
    ax.plot([xs[a],xs[b]],[nodes[a][2],nodes[b][2]],[depth[a],depth[b]],color='0.5',lw=0.6)
for i,n in enumerate(nodes):
    if n[0]==0 and i not in children: continue
    col='k' if i in sols else ('0.3' if n[0]==K-2 else 'white')
    if i in sols: continue
    ax.scatter([xs[i]],[n[2]],[n[0]],s=14,c=col,edgecolor='k',depthshade=False)
for i in sols:
    ax.scatter([xs[i]],[nodes[i][2]],[nodes[i][0]],s=170,c='k',marker='*',depthshade=False,zorder=10)
    ax.text(xs[i],nodes[i][2],nodes[i][0]+0.55,'$\\{5,5,9,9,89\\}$',fontsize=9,ha='center')
ax.set_zlabel('depth $j$'); ax.set_ylabel('$M$'); ax.set_xlabel('branches'); ax.set_xticks([])
ax.invert_zaxis(); ax.view_init(elev=18,azim=-70)
for a in (ax.xaxis,ax.yaxis,ax.zaxis): a.pane.set_facecolor((1,1,1,0)); a.pane.set_edgecolor('0.6')
fig.savefig(OUT+'tree.png',dpi=220,bbox_inches='tight'); plt.close(fig)
print('tree nodes',len(nodes),'sols',[nodes[s] for s in sols])

# 5. tree sizes by k for modes (3D bars)
data={'Z':{2:2,3:4,4:9,5:15,6:24,7:39,8:64,9:101,10:147,11:231,12:426,13:1446,14:32489},
 'U':{2:2,3:4,4:14,5:44,6:193,7:9242},
 'Q':{2:2,3:4,4:13,5:32,6:116,7:7159},
 'G':{2:2,3:3,4:7,5:13,6:22,7:41,8:87,9:402,10:16230},
 'E':{2:2,3:4,4:8,5:13,6:20,7:32,8:49,9:80,10:119,11:195,12:332,13:856,14:8517}}
import pickle; pickle.dump(data,open('counts.pkl','wb'))
fig=plt.figure(figsize=(7.0,4.6)); ax=fig.add_subplot(111,projection='3d')
modes=['Z','U','Q','G','E']; shades=['0.15','0.35','0.55','0.72','0.88']
for i,mname in enumerate(modes):
    ks=sorted(data[mname]); hs=[math.log10(data[mname][k]) for k in ks]
    ax.bar3d(np.array(ks)-0.3,[i]*len(ks),[0]*len(ks),0.6,0.5,hs,color=shades[i],edgecolor='k',linewidth=0.3,shade=True)
ax.set_yticks(range(5)); ax.set_yticklabels(['$\\mathsf{'+m+'}$' for m in modes]); ax.set_xlabel('$k$'); ax.set_zlabel('$\\log_{10}$ nodes')
ax.view_init(elev=24,azim=-62)
for a in (ax.xaxis,ax.yaxis,ax.zaxis): a.pane.set_facecolor((1,1,1,0)); a.pane.set_edgecolor('0.6')
fig.savefig(OUT+'counts.png',dpi=220,bbox_inches='tight'); plt.close(fig)
