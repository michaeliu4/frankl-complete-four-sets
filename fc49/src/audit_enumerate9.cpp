// Independent exhaustive 9-point augmentation audit.
// Input: a binary 7-point allowed table (uint64 masks), then text boundary file
// with lines: block_count subset_mask ... . All 4-sets use numeric-mask order.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <unordered_set>
#include <vector>
#include <functional>
#include <string>
using namespace std;
using U=uint64_t; using W=__uint128_t;
struct Hash{size_t operator()(W x)const {return U(x)^(U(x>>64)*0x9e3779b97f4a7c15ULL);}};
vector<int>edges[10]; int idx[10][512];
unordered_set<U> allowed7;
array<unordered_set<W,Hash>,12> allowed8;
vector<vector<int>> bases; vector<int>triples;
U change7[56][28]; W change8[56][8];
array<pair<int,int>,28> omit;
long long visits=0,leaves=0,pruned7=0,pruned8=0,pruneddeg=0;
int compress(int s,int removed) {int t=0,j=0;for(int i=0;i<9;i++)if(!(removed>>i&1)){if(s>>i&1)t|=1<<j;j++;}return t;}
bool acceptable8(W s) {int m=__builtin_popcountll(U(s))+__builtin_popcountll(U(s>>64));if(m>=12)return false;return m<9||allowed8[m].count(s);}
int main(int argc,char**argv){
 try{
  if(argc<3)throw runtime_error("expected 7-point table and 8-point bases");
  for(auto &row:idx)fill(begin(row),end(row),-1);
  for(int n=7;n<=9;n++)for(int s=0;s<(1<<n);s++)if(__builtin_popcount((unsigned)s)==4){idx[n][s]=edges[n].size();edges[n].push_back(s);}
  {ifstream f(argv[1],ios::binary);if(!f)throw runtime_error("missing table");U s;while(f.read((char*)&s,sizeof s))allowed7.insert(s);if(!f.eof())throw runtime_error("bad table");}
  if(allowed7.size()!=665022)throw runtime_error("wrong 7-point table size");
  {ifstream f(argv[2]);int m;while(f>>m){if(m<9||m>11)throw runtime_error("bad base size");vector<int>A(m);unordered_set<int>seen;for(int&a:A){if(!(f>>a)||a<0||a>=256||idx[8][a]<0||!seen.insert(a).second)throw runtime_error("bad base");}bases.push_back(A);}}
  array<int,8>p{0,1,2,3,4,5,6,7};do {int map[256]={};for(int s=1;s<256;s++){int i=__builtin_ctz((unsigned)s);map[s]=map[s^(1<<i)]|1<<p[i];}for(auto const&A:bases){W k=0;for(int a:A)k|=W(1)<<idx[8][map[a]];allowed8[A.size()].insert(k);}}while(next_permutation(p.begin(),p.end()));
  for(int m=9;m<=11;m++)cerr<<"allowed "<<m<<" labeled "<<allowed8[m].size()<<"\n";
  for(int s=0;s<256;s++)if(__builtin_popcount((unsigned)s)==3)triples.push_back(s);
  int z=0;for(int i=0;i<8;i++)for(int j=i+1;j<8;j++)omit[z++]={i,j};
  for(int a=0;a<56;a++){
   int s=triples[a]|256;
   for(int i=0;i<8;i++)if(!(s>>i&1))change8[a][i]=W(1)<<idx[8][compress(s,1<<i)];
   for(int k=0;k<28;k++){auto [i,j]=omit[k];if(!(s&((1<<i)|(1<<j))))change7[a][k]=U(1)<<idx[7][compress(s,(1<<i)|(1<<j))];}
  }
  // Two independent necessary degree tests can be disabled for cross-checking.
  bool use7=argc<4||string(argv[3])!="no7";
  bool useDeg=argc<4||string(argv[3])!="nodegree";
  int cases=0;
  for(auto const&base:bases){
   int d=16-base.size();if(d<5||d>7)throw runtime_error("bad delta");
   array<int,8>deg{};array<W,8>r8{};array<U,28>r7{};vector<int>selected;
   for(int a:base){for(int i=0;i<8;i++){deg[i]+=a>>i&1;if(!(a>>i&1))r8[i]|=W(1)<<idx[8][compress(a,1<<i)];}for(int k=0;k<28;k++){auto[i,j]=omit[k];if(!(a&((1<<i)|(1<<j))))r7[k]|=U(1)<<idx[7][compress(a,(1<<i)|(1<<j))];}}
   function<void(int,int,array<int,8>const&,array<W,8>const&,array<U,28>const&)> dfs;
   dfs=[&](int first,int left,array<int,8>const&dd,array<W,8>const&rr8,array<U,28>const&rr7){
    visits++;
    if(useDeg){
     for(int i=0;i<8;i++){
      int available=0;for(int j=first;j<56;j++)available+=triples[j]>>i&1;
      int avoid=(56-first)-available;
      int low=dd[i]+max(0,left-avoid),high=dd[i]+min(left,available);
      if(high<d||low>64-8*d){pruneddeg++;return;}
     }
    }
    if(left==0){
     // Actual minimum degree is checked even when the intermediate test is disabled.
     if(*min_element(dd.begin(),dd.end())<d)return;
     leaves++;cout<<"SURVIVOR";for(int a:base)cout<<' '<<a;for(int a:selected)cout<<' '<<a;cout<<'\n';return;
    }
    for(int j=first;j<=56-left;j++){
     auto tt7=rr7;auto tt8=rr8;auto ttdeg=dd;bool ok=true;
     if(use7)for(int k=0;k<28;k++){
      tt7[k]|=change7[j][k];if(!allowed7.count(tt7[k])){ok=false;pruned7++;break;}
     }
     if(!ok)continue;
     for(int i=0;i<8;i++){
      tt8[i]|=change8[j][i];if(!acceptable8(tt8[i])){ok=false;pruned8++;break;}
      ttdeg[i]+=triples[j]>>i&1;
     }
     if(!ok)continue;
     selected.push_back(triples[j]|256);dfs(j+1,left-1,ttdeg,tt8,tt7);selected.pop_back();
    }
   };
   dfs(0,d,deg,r8,r7);cases++;
   if(cases%10==0)cerr<<"completed bases "<<cases<<" visits "<<visits<<" leaves "<<leaves<<"\n";
  }
  cout<<"DONE cases "<<cases<<" visits "<<visits<<" leaves "<<leaves<<" pruned7 "<<pruned7<<" pruned8 "<<pruned8<<" pruneddeg "<<pruneddeg<<"\n";
  return leaves?1:0;
 }catch(exception const&e){cerr<<e.what()<<'\n';return 2;}
}
