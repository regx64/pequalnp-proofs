// Enumerate all canonical AO2 circuits (AND/OR, two distinct earlier wires, no copy gate, all wire
// functions distinct, every non-output gate read) of exactly S gates computing the edge function of
// a graph on n<=6 vertices (all 64 rows), and classify each by its read number:
// read(C) = max over edges e of (least k such that some proof tree of e reads each endpoint <= k).
#include <bits/stdc++.h>
using namespace std; typedef uint64_t M;
int n,S; M T; vector<M> w; vector<int> ga,gb,gop,readc; vector<pair<int,int>> E;
long long found=0; long long hist[8]={0}; long long nodes=0; long long limitFound=LLONG_MAX;
// Pareto sets of (ca,cb) capped at CAP
const int CAP=4;
int readNumber(){
  int W=n+S, worst=0;
  for(auto&e:E){
    // sets as bitmask over (ca,cb) in [0..CAP]x[0..CAP] -> 25 bits
    vector<uint32_t> R(W,0);
    auto bit=[&](int a,int b){return 1u<<(min(a,CAP)*(CAP+1)+min(b,CAP));};
    R[e.first]=bit(1,0); R[e.second]=bit(0,1);
    for(int j=0;j<S;j++){
      uint32_t A=R[ga[j]],B=R[gb[j]],out=0;
      if(gop[j]) out=A|B;
      else for(int x=0;x<25;x++) if(A>>x&1) for(int y=0;y<25;y++) if(B>>y&1){
        int a=x/5+y/5,b=x%5+y%5; out|=bit(a,b);}
      R[n+j]=out;
    }
    uint32_t O=R[W-1]; int best=99;
    for(int x=0;x<25;x++) if(O>>x&1){ int k=max(x/5,x%5); best=min(best,k);}
    worst=max(worst,best);
  }
  return worst;
}
vector<string> examples[8];
void dfs(int j){
  nodes++;
  int W=n+j; int un=0; for(int k=0;k<W;k++) if(!readc[k]) un++;
  if(un-1 > S-j) return;
  if(j==S){ if(un==1 && w[W-1]==T){ found++; int r=readNumber(); hist[min(r,7)]++;
      if(examples[min(r,7)].size()<2){ string s; for(int q=0;q<S;q++){ s+= "w"+to_string(n+q)+"="+(gop[q]?"OR":"AND")+"(w"+to_string(ga[q])+",w"+to_string(gb[q])+") ";} examples[min(r,7)].push_back(s);} }
    return; }
  for(int b=1;b<W;b++) for(int a=0;a<b;a++) for(int op=0;op<2;op++){
    if(j>0 && b!=W-1 && a!=W-1){ if(make_tuple(b,a,op) < make_tuple(gb[j-1],ga[j-1],gop[j-1])) continue; }
    M v= op? (w[a]|w[b]) : (w[a]&w[b]);
    if(v==w[a]||v==w[b]) continue;
    bool dup=false; for(int k=0;k<W;k++) if(w[k]==v){dup=true;break;} if(dup) continue;
    if(j==S-1 && v!=T) continue;
    w.push_back(v); ga[j]=a; gb[j]=b; gop[j]=op; readc[a]++; readc[b]++; readc.push_back(0);
    dfs(j+1);
    w.pop_back(); readc[a]--; readc[b]--; readc.pop_back();
  }
}
int main(int argc,char**argv){
  S=atoi(argv[1]); n=atoi(argv[2]);
  { stringstream ss(argv[3]); string t; while(getline(ss,t,',')){ int p=t.find('-'); E.push_back({stoi(t.substr(0,p)),stoi(t.substr(p+1))}); } }
  int R=1<<n;
  for(int i=0;i<n;i++){ M m=0; for(int r=0;r<R;r++) if(r>>i&1) m|=1ULL<<r; w.push_back(m); }
  T=0; for(int r=0;r<R;r++){ bool f=false; for(auto&e:E) if((r>>e.first&1)&&(r>>e.second&1)) f=true; if(f) T|=1ULL<<r; }
  ga.assign(S,0); gb.assign(S,0); gop.assign(S,0); readc.assign(n,0);
  dfs(0);
  printf("S=%d circuits=%lld",S,found); for(int r=1;r<8;r++) if(hist[r]) printf(" read%d:%lld",r,hist[r]); printf("\n");
  for(int r=3;r<8;r++) for(auto&s:examples[r]) printf("  ex read%d: %s\n",r,s.c_str());
}
