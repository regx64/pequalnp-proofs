// For every minimum circuit (enumeration as in enumrk), apply the move to a fixed point:
//   an OR gate g outside the top OR-tree with an operand w below F: replace every read of g by
//   g's other operand, delete g, add a new output OR(old output, w). Size is unchanged.
// Then classify the normalized circuit by read number. Report histograms before/after.
#include <bits/stdc++.h>
using namespace std; typedef uint64_t M;
int n,S; M T; vector<pair<int,int>> E;
struct G{int op,a,b;};
vector<M> inputs;
vector<M> evalc(const vector<G>& gs){ vector<M> v=inputs; for(auto&g:gs) v.push_back(g.op? (v[g.a]|v[g.b]) : (v[g.a]&v[g.b])); return v; }
int readNum(const vector<G>& gs, int out){
  const int CAP=4; int W=n+gs.size(), worst=0;
  auto bit=[&](int a,int b){return 1u<<(min(a,CAP)*(CAP+1)+min(b,CAP));};
  for(auto&e:E){ vector<uint32_t> R(W,0); R[e.first]=bit(1,0); R[e.second]=bit(0,1);
    for(size_t j=0;j<gs.size();j++){ uint32_t A=R[gs[j].a],B=R[gs[j].b],o=0;
      if(gs[j].op) o=A|B; else for(int x=0;x<25;x++) if(A>>x&1) for(int y=0;y<25;y++) if(B>>y&1) o|=bit(x/5+y/5,x%5+y%5);
      R[n+j]=o; }
    uint32_t O=R[out]; int best=99; for(int x=0;x<25;x++) if(O>>x&1) best=min(best,max(x/5,x%5)); worst=max(worst,best); }
  return worst;
}
// normalize; returns -1 on loop
vector<G> lastNorm; int lastOut;
int normalize(vector<G> gs, int& outRead, string& desc){
  int out=n+gs.size()-1;
  for(int it=0; it<60; it++){
    vector<M> v=evalc(gs); int W=v.size();
    // top OR tree
    vector<char> top(W,0); vector<int> st; if(out>=n && gs[out-n].op==1){ st.push_back(out); }
    while(!st.empty()){ int x=st.back(); st.pop_back(); if(top[x]) continue; top[x]=1; G&g=gs[x-n];
      for(int c: {g.a,g.b}) if(c>=n && gs[c-n].op==1) st.push_back(c); }
    int pick=-1, wsel=-1;
    for(int j=0;j<(int)gs.size() && pick<0;j++){ int x=n+j; if(top[x]||x==out||gs[j].op!=1) continue;
      for(int c: {gs[j].a,gs[j].b}) if((v[c]&~T)==0){ pick=j; wsel=c; break; } }
    if(pick<0){ outRead=readNum(gs,out); lastNorm=gs; lastOut=out; return it; }
    int z = (gs[pick].a==wsel)? gs[pick].b : gs[pick].a;
    int gx=n+pick;
    // rebuild without gate pick; remap indices
    vector<G> ng; auto mp=[&](int i){ if(i==gx) i=z; return i>gx? i-1 : i; };
    for(int j=0;j<(int)gs.size();j++) if(j!=pick){ G g=gs[j]; g.a=mp(g.a); g.b=mp(g.b); ng.push_back(g); }
    int nout=mp(out); int nw=mp(wsel);
    ng.push_back({1,min(nout,nw),max(nout,nw)}); out=n+ng.size()-1; gs=ng;
    // sanity: function preserved
    vector<M> v2=evalc(gs); if(v2[out]!=T){ desc="FUNCTION CHANGED"; return -2; }
  }
  return -1;
}
// can one gate be deleted, its reads (and the output, if it is the output) redirected to another wire t?
string redundantGate(const vector<G>& gs, int out){
  int W=n+gs.size();
  for(int j=0;j<(int)gs.size();j++){ int x=n+j; int minReader=W; for(int q=0;q<(int)gs.size();q++) if(gs[q].a==x||gs[q].b==x) minReader=min(minReader,n+q);
    for(int t=0;t<W;t++){ if(t==x) continue; if(t>=minReader) continue;
      // build: replace reads of x by t, delete gate j
      vector<G> ng; auto mp=[&](int i){ if(i==x) i=t; return i>x? i-1 : i; };
      bool okOrder=true;
      for(int q=0;q<(int)gs.size();q++) if(q!=j){ G g=gs[q]; g.a=mp(g.a); g.b=mp(g.b); if(g.a>=n+(int)ng.size()||g.b>=n+(int)ng.size()) okOrder=false; ng.push_back(g); }
      if(!okOrder) continue;
      int no = (out==x)? mp(t) : mp(out);
      vector<M> v=evalc(ng); if(no<(int)v.size() && v[no]==T) return "delete w"+to_string(x)+" use w"+to_string(t);
    } }
  return "";
}
long long badCount=0, badNoRed=0; vector<string> noRedEx;
vector<M> w; vector<int> ga,gb,gop,readc; long long found=0; map<pair<int,int>,long long> hist; vector<string> bad;
void dfs(int j){
  int W=n+j; int un=0; for(int k=0;k<W;k++) if(!readc[k]) un++;
  if(un-1 > S-j) return;
  if(j==S){ if(un==1 && w[W-1]==T){ found++; vector<G> gs; for(int q=0;q<S;q++) gs.push_back({gop[q],ga[q],gb[q]});
      int r0=readNum(gs,n+S-1); int r1=-9; string d; int st=normalize(gs,r1,d); if(st<0) r1=st;
      hist[{r0,r1}]++;
      if(r1>=3){ badCount++; string rr=redundantGate(lastNorm,lastOut); if(rr.empty()){ badNoRed++; if(noRedEx.size()<4){ string s; for(auto&g:lastNorm) s+=string(g.op?"OR":"AND")+"("+to_string(g.a)+","+to_string(g.b)+") "; noRedEx.push_back(s);} } }
      if(r1>=3 || r1<0){ if(bad.size()<3){ string s; for(auto&g:gs) s+=string(g.op?"OR":"AND")+"("+to_string(g.a)+","+to_string(g.b)+") "; bad.push_back(s+" -> "+to_string(r1)+" "+d);} } }
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
  vector<long long> rows; { stringstream ss(argv[4]); string t; while(getline(ss,t,',')) rows.push_back(stoll(t)); }
  int R=rows.size(); if(R>64){ printf("too many rows\n"); return 1; }
  for(int i=0;i<n;i++){ M m=0; for(int r=0;r<R;r++) if(rows[r]>>i&1) m|=1ULL<<r; inputs.push_back(m); }
  w=inputs; T=0; for(int r=0;r<R;r++){ bool f=false; for(auto&e:E) if((rows[r]>>e.first&1)&&(rows[r]>>e.second&1)) f=true; if(f) T|=1ULL<<r; }
  ga.assign(S,0); gb.assign(S,0); gop.assign(S,0); readc.assign(n,0);
  dfs(0);
  printf("S=%d circuits=%lld  (read before -> read after normalization):",S,found);
  for(auto&[k,c]:hist) printf(" %d->%d:%lld",k.first,k.second,c); printf("\n");
  printf("  normalized read>=3: %lld, of which with NO deletable gate: %lld\n",badCount,badNoRed);
  for(auto&s:noRedEx) printf("  NO-REDUNDANT: %s\n",s.c_str());
}
