// Lehmer multiset search.  Usage: lms MODE SIGN K [Mmin Mmax]
// MODE: int uni quad gauss eis ;  SIGN -1 (Lehmer N-1=M phi) or +1 (companion N+1=M phi)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <gmp.h>
typedef unsigned long long u64; typedef __uint128_t u128;
static int MODE, SIGN, K; static mpz_t XMAX; static int HAVEX=0; static long CURM; static long long nodes=0, terms=0, cands=0, nsol=0, skiplo=0, caphi=0, bigx=0;
enum {INT,UNI,QUAD,GAUSS,EIS};
static u64 mulmod(u64 a,u64 b,u64 m){return (u128)a*b%m;}
static u64 powmod(u64 a,u64 e,u64 m){u64 r=1;a%=m;while(e){if(e&1)r=mulmod(r,a,m);a=mulmod(a,a,m);e>>=1;}return r;}
static int isprime64(u64 n){ if(n<2)return 0; static const u64 sp[]={2,3,5,7,11,13,17,19,23,29,31,37};
 for(int i=0;i<12;i++){if(n%sp[i]==0)return n==sp[i];}
 u64 d=n-1;int s=0;while(!(d&1)){d>>=1;s++;}
 for(int i=0;i<12;i++){u64 a=sp[i];u64 x=powmod(a,d,n);if(x==1||x==n-1)continue;int ok=0;for(int r=1;r<s;r++){x=mulmod(x,x,n);if(x==n-1){ok=1;break;}}if(!ok)return 0;}
 return 1;}
static u64 iroot(u64 n,int e){ u64 r=(u64)1; // floor n^(1/e)
 u64 lo=1,hi=(e==2)?4294967296ULL:(e==3?2642246ULL:65536ULL);
 while(lo<hi){u64 mid=(lo+hi+1)/2; u128 p=1;int over=0;for(int i=0;i<e;i++){p*=mid;if(p>n){over=1;break;}} if(!over&&p<=n)lo=mid;else hi=mid-1;} r=lo; return r;}
// returns base prime p and exponent f if n is odd prime power, else 0
static u64 ppow(u64 n,int*f){ if(n<3||!(n&1))return 0; if(isprime64(n)){*f=1;return n;}
 for(int e=2;e<=40;e++){u64 r=iroot(n,e); if(r<3)break; u128 p=1;for(int i=0;i<e;i++)p*=r; if(p==n&&isprime64(r)){*f=e;return r;}}
 return 0;}

static unsigned *basep=0; static int nbase=0; static u64 *pp2=0; static long npp2=0;
static void initsieve(void){ int L=10000000; char*c=calloc(L+1,1); basep=malloc(sizeof(unsigned)*700000);
 for(int i=2;i<=L;i++){ if(!c[i]){ basep[nbase++]=i; for(long j=(long)i*i;j<=L;j+=i)c[j]=1; } }
 free(c); pp2=malloc(sizeof(u64)*2000000);
 for(int i=1;i<nbase;i++){ u128 x=(u128)basep[i]*basep[i]; while(x<=(u128)100000000000000ULL){ pp2[npp2++]=(u64)x; x*=basep[i]; } }
 // sort
 int cmp(const void*a,const void*b){u64 x=*(u64*)a,y=*(u64*)b;return x<y?-1:x>y;} qsort(pp2,npp2,sizeof(u64),cmp);}
// fill buffer with odd prime powers in [lo,hi]
static u64 *buf=0; static long bufcap=0;
static long ppow_range(u64 lo,u64 hi){ long n=0; if(lo<3)lo=3; if(hi<lo) return 0;
 if(hi-lo<=20000 || hi>100000000000000ULL){ for(u64 q=lo|1;q<=hi;q+=2){int f; if(ppow(q,&f)){ if(n>=bufcap){bufcap=bufcap?2*bufcap:1<<20; buf=realloc(buf,bufcap*sizeof(u64));} buf[n++]=q;} } return n; }
 u64 len=hi-lo+1; char*c=calloc(len,1); if(!c){fprintf(stderr,"FATAL calloc %llu\n",len); exit(3);}
 for(int i=0;i<nbase;i++){ u64 p=basep[i]; if(p*p>hi)break; u64 st=((lo+p-1)/p)*p; if(st<p*p) st=p*p; for(u64 j=st;j<=hi;j+=p) c[j-lo]=1; }
 // merge with prime powers e>=2
 long a=0; while(a<npp2 && pp2[a]<lo) a++;
 for(u64 q=lo;q<=hi;q++){ int isp = (q&1) && !c[q-lo];
   if(!isp){ while(a<npp2 && pp2[a]<q) a++; if(a<npp2 && pp2[a]==q) isp=1; }
   if(isp){ if(n>=bufcap){bufcap=bufcap?2*bufcap:1<<20; buf=realloc(buf,bufcap*sizeof(u64));} buf[n++]=q; } }
 free(c); return n; }

static u64 seqv[64]; static u64 seqp[64]; static int seqf[64];
static int allowed(int j,u64 q,u64 p,int f){ // seq[0..j-1] fixed, sorted nondecreasing
 if(j>0 && q<seqv[j-1]) return 0;
 for(int i=0;i<j;i++){ if((q-1)%seqp[i]==0) return 0; if((seqv[i]-1)%p==0) return 0; }
 if(CURM%p==0) return 0;
 int same=0; for(int i=0;i<j;i++) if(seqp[i]==p) same++;
 switch(MODE){
 case INT: return f==1 && (j==0||q>seqv[j-1]);
 case UNI: return 1;
 case QUAD: if(f==1) {for(int i=0;i<j;i++) if(seqp[i]==p && seqf[i]!=1) return 0; return same<2;}
            if(f==2) return same==0; return 0;
 case GAUSS: if(f==1) return (p%4==1)&&same<2; if(f==2) return (p%4==3)&&same==0; return 0;
 case EIS: if(f==1){ if(p==3) return same==0; return (p%3==1)&&same<2;} if(f==2) return (p%3==2)&&same==0; return 0;
 } return 0;}
static void printsol(u64 q, mpz_t x, long M){ nsol++; printf("SOL M=%ld :",M); for(int i=0;i<K-2;i++)printf(" %llu",seqv[i]); printf(" %llu ",q); mpz_out_str(stdout,10,x); printf("\n"); fflush(stdout);}
static mpz_t T1,T2,T3,Dz,Cz,MBz,uz,vz,xz;
// test whether (q/(q-1))^m * A > M*B, i.e. A q^m > M B (q-1)^m
static int reach(mpz_t A,mpz_t B,long M,u64 q,int m){ mpz_set(T1,A); mpz_set_ui(T2,1); for(int i=0;i<m;i++){mpz_mul_ui(T1,T1,q);} mpz_mul_si(T2,B,M); for(int i=0;i<m;i++) mpz_mul_ui(T2,T2,q-1); if(SIGN>0) mpz_add_ui(T1,T1,2); return mpz_cmp(T1,T2)>0;}
static int xok(mpz_t x,u64 q,int j,u64 qq,u64 pq,int fq){ // x as last element, j index = K-1
 if(mpz_cmp_ui(x,q)<0) return 0;
 { mpz_t t; mpz_init(t); mpz_sub_ui(t,x,1); for(int i=0;i<K-2;i++) if(mpz_divisible_ui_p(t,seqp[i])){mpz_clear(t);return 0;} if(mpz_divisible_ui_p(t,pq)){mpz_clear(t);return 0;} mpz_clear(t);} 
 if(!mpz_fits_ulong_p(x)){ // big: check prime only (possible prime power rare) 
   if(mpz_even_p(x)) return 0; int r=mpz_probab_prime_p(x,30); if(r){ if(MODE==INT||MODE==UNI||MODE==QUAD) return 1; mpz_t t;mpz_init(t); unsigned long m4=mpz_fdiv_ui(x,4), m3=mpz_fdiv_ui(x,3); mpz_clear(t); if(MODE==GAUSS) return m4==1; if(MODE==EIS) return m3==1; } 
   if(mpz_perfect_power_p(x)){ fprintf(stderr,"WARN big perfect power last elt\n"); return 2;} return 0; }
 u64 X=mpz_get_ui(x); int f; u64 p=ppow(X,&f); if(!p) return 0;
 seqv[K-2]=qq; seqp[K-2]=pq; seqf[K-2]=fq; return allowed(K-1,X,p,f);}
static void rec(mpz_t A,mpz_t B,int j,long M){
 nodes++; int m=K-j;
 if(MODE==INT && j>=1 && seqv[0]==3){ long r=CURM%3; if(SIGN<0 && r!=1) return; if(SIGN>0 && r!=2) return; }
 mpz_mul_si(MBz,B,M); mpz_sub(Cz,MBz,A); if(mpz_sgn(Cz)<=0) return;
 // lo: q > MB/C
 mpz_fdiv_q(T3,MBz,Cz); if(!mpz_fits_ulong_p(T3)||mpz_cmp_ui(T3,(1ULL<<62))>=0){ mpz_set_ui(T1,(1ULL<<62)); if(reach(A,B,M,(1ULL<<62),m)) skiplo++; return;} u64 lo=mpz_get_ui(T3)+1; if(j>0&&lo<seqv[j-1]) lo=seqv[j-1]; if(lo<3) lo=3;
 if(!reach(A,B,M,lo,m)) return;
 u64 hi=lo; while(hi<(1ULL<<62) && reach(A,B,M,hi*2,m)) hi*=2; if(hi>=(1ULL<<62)) caphi++; {u64 a=hi,b=hi*2; while(b-a>1){u64 c=a+(b-a)/2; if(reach(A,B,M,c,m))a=c; else b=c;} hi=a;}
 if(HAVEX){ mpz_t t; mpz_init(t); mpz_fdiv_q(t,XMAX,A); mpz_root(t,t,m); if(mpz_cmp_ui(t,hi)<0) hi=mpz_get_ui(t); mpz_clear(t); if(hi<lo) return; }
 if(m==2){ terms++;
   mpz_t A2,B2; mpz_inits(A2,B2,NULL);
   long nb=ppow_range(lo,hi); u64*lb=malloc(nb*sizeof(u64)+8); memcpy(lb,buf,nb*sizeof(u64));
   for(long ii=0;ii<nb;ii++){ u64 q=lb[ii]; int f; u64 p=ppow(q,&f); if(!p) continue; if(!allowed(j,q,p,f)) continue; cands++;
     mpz_mul_ui(A2,A,q); mpz_mul_ui(B2,B,q-1); mpz_mul_si(B2,B2,M); // B2 = M B (q-1)
     mpz_sub(Cz,B2,A2); if(mpz_sgn(Cz)<=0) continue; // den
     if(SIGN<0) mpz_sub_ui(T1,B2,1); else mpz_add_ui(T1,B2,1);
     if(mpz_divisible_p(T1,Cz)){ mpz_divexact(xz,T1,Cz); int r=xok(xz,q,j,q,p,f); if(r) printsol(q,xz,M);} }
   free(lb); mpz_clears(A2,B2,NULL); return; }
 mpz_t A2,B2; mpz_inits(A2,B2,NULL);
 long nb=ppow_range(lo,hi); u64*lb=malloc(nb*sizeof(u64)+8); memcpy(lb,buf,nb*sizeof(u64));
 for(long ii=0;ii<nb;ii++){ u64 q=lb[ii]; int f; u64 p=ppow(q,&f); if(!p) continue; if(!allowed(j,q,p,f)) continue;
   seqv[j]=q; seqp[j]=p; seqf[j]=f; mpz_mul_ui(A2,A,q); mpz_mul_ui(B2,B,q-1); rec(A2,B2,j+1,M); }
 free(lb); mpz_clears(A2,B2,NULL);}
int main(int argc,char**argv){ initsieve();
 const char*md=argv[1]; MODE=!strcmp(md,"int")?INT:!strcmp(md,"uni")?UNI:!strcmp(md,"quad")?QUAD:!strcmp(md,"gauss")?GAUSS:EIS;
 SIGN=atoi(argv[2]); K=atoi(argv[3]); long Mmin=2,Mmax=1; { double p=1; for(int i=0;i<K;i++)p*=1.5; Mmax=(long)p+1;} if(argc>5){Mmin=atol(argv[4]);Mmax=atol(argv[5]);}
 if(SIGN>0) Mmin = Mmin<1?1:Mmin;  mpz_init(XMAX); if(argc>6){ mpz_ui_pow_ui(XMAX,10,atol(argv[6])); HAVEX=1; } 
 mpz_inits(T1,T2,T3,Dz,Cz,MBz,uz,vz,xz,NULL); mpz_t A,B; mpz_inits(A,B,NULL);
 for(long M=Mmin;M<=Mmax;M++){ CURM=M; mpz_set_ui(A,1); mpz_set_ui(B,1); rec(A,B,0,M);} 
 printf(HAVEX?"DONE(n<10^%s) ":"%s",HAVEX?argv[6]:""); printf("DONE mode=%s sign=%d K=%d nodes=%lld terminal=%lld cands=%lld sols=%lld skiplo=%lld caphi=%lld\n",md,SIGN,K,nodes,terms,cands,nsol,skiplo,caphi); return 0;}
