#include <bits/stdc++.h>
using namespace std;
struct Dinic {
 struct E {int to,rev; long long cap;};
 vector<vector<E>> g; vector<int> level,it;
 Dinic(int n):g(n),level(n),it(n){}
 void add(int a,int b,long long c){if(a==b||!c)return; E x{b,(int)g[b].size(),c},y{a,(int)g[a].size(),0};g[a].push_back(x);g[b].push_back(y);}
 bool bfs(int s,int t){fill(level.begin(),level.end(),-1);queue<int>q;level[s]=0;q.push(s);while(!q.empty()){int v=q.front();q.pop();for(auto&e:g[v])if(e.cap>0&&level[e.to]<0){level[e.to]=level[v]+1;q.push(e.to);}}return level[t]>=0;}
 long long dfs(int v,int t,long long f){if(v==t)return f;for(int&i=it[v];i<(int)g[v].size();++i){E&e=g[v][i];if(e.cap>0&&level[e.to]==level[v]+1){long long d=dfs(e.to,t,min(f,e.cap));if(d){e.cap-=d;g[e.to][e.rev].cap+=d;return d;}}}return 0;}
 long long flow(int s,int t){long long ans=0,d;while(bfs(s,t)){fill(it.begin(),it.end(),0);while((d=dfs(s,t,INT_MAX/2)))ans+=d;}return ans;}
};
using Bits=bitset<512>; vector<int> seeds;
vector<vector<int>> automaps;
int n,N,INF,NEG;vector<int>A,AC,qv;vector<pair<int,int>>basearcs;long long nodes=0,leaves=0,conflicts=0;int maxdepth=0;double limitsec=0;chrono::steady_clock::time_point started;bool stopped=false;vector<int>counterex; ofstream proofout;
bool UC(const Bits&B){for(int s=0;s<N;s++)if(B[s])for(int t=s+1;t<N;t++)if(B[t]&&!B[s|t])return false;return true;}
Bits extend(Bits const&F,int s){Bits D=F;for(int a:AC){int u=s|a;D[u]=1;for(int t=0;t<N;t++)if(F[t])D[u|t]=1;}return D;}
Bits orbit(Bits const&F,Bits const&Z,int s){
 Bits O; O[s]=1;
 for(auto const&p:automaps){
  bool ok=true;
  for(int t=0;t<N;t++)if((F[t]&&!F[p[t]])||(Z[t]&&!Z[p[t]])){ok=false;break;}
  if(ok)O[p[s]]=1;
 }
 return O;
}
// Return 0 if all share-negative families excluded; 1 on counterexample; 2 timeout.
int search(Bits F,Bits Z,int dep){
 ++nodes;maxdepth=max(maxdepth,dep);
 if(nodes%500==0){double sec=chrono::duration<double>(chrono::steady_clock::now()-started).count();if(limitsec>0 && sec>limitsec){stopped=true;return 2;}if(nodes%5000==0)cerr<<nodes<<" nodes "<<sec<<" seconds depth "<<dep<<" leaves "<<leaves<<"\n";}
 if((F&Z).any()){conflicts++;if(proofout.is_open())proofout<<"C\n";return 0;}
 Dinic g(N+2);
 for(int s=0;s<N;s++){if(qv[s]<0)g.add(N,s,-qv[s]);if(qv[s]>0)g.add(s,N+1,qv[s]);if(F[s])g.add(N,s,INF);if(Z[s])g.add(s,N+1,INF);}
 for(auto [s,t]:basearcs)g.add(s,t,INF);
 for(int s:seeds)for(int t=0;t<N;t++)if((s|t)!=t)g.add(t,s|t,INF);
 long long bound=g.flow(N,N+1)-NEG;
 if(bound>=0){leaves++;if(proofout.is_open())proofout<<"L\n";return 0;}
 Bits B;vector<int>vis(N+2);queue<int>que;que.push(N);vis[N]=1;
 while(!que.empty()){int s=que.front();que.pop();for(auto&e:g.g[s])if(e.cap>0&&!vis[e.to]){vis[e.to]=1;que.push(e.to);}}
 for(int s=0;s<N;s++)if(vis[s])B[s]=1;
 vector<int>score(N);int violations=0;
 for(int s=0;s<N;s++)if(B[s])for(int t=s+1;t<N;t++)if(B[t]&&!B[s|t]){score[s]++;score[t]++;violations++;}
 if(!violations){for(int s=0;s<N;s++)if(B[s])counterex.push_back(s);return 1;}
 int chosen=-1,sc=-1;
 for(int s=0;s<N;s++)if(!F[s]&&!Z[s]&&score[s]>sc){sc=score[s];chosen=s;}
 if(chosen<0||sc<=0){cerr<<"internal error\n";exit(3);}
 Bits O=orbit(F,Z,chosen);if(proofout.is_open())proofout<<"O "<<chosen<<"\n";
 Bits plus=extend(F,chosen);seeds.push_back(chosen);int r=search(plus,Z,dep+1);seeds.pop_back();if(r)return r;
 Z|=O;return search(F,Z,dep+1);
}
int replay(istream &in, Bits F, Bits Z,int dep){
 ++nodes;maxdepth=max(maxdepth,dep);string tag;
 if(!(in>>tag))throw runtime_error("truncated certificate");
 if(tag=="C") {if((F&Z).none())throw runtime_error("false conflict");conflicts++;return 0;}
 if(tag=="B"||tag=="O") {int s;if(!(in>>s)||s<0||s>=N||F[s]||Z[s])throw runtime_error("invalid split");Bits O;if(tag=="O")O=orbit(F,Z,s);else O[s]=1;seeds.push_back(s);replay(in,extend(F,s),Z,dep+1);seeds.pop_back();Z|=O;replay(in,F,Z,dep+1);return 0;}
 if(tag!="L")throw runtime_error("unknown certificate token");
 Dinic g(N+2);
 for(int s=0;s<N;s++){if(qv[s]<0)g.add(N,s,-qv[s]);if(qv[s]>0)g.add(s,N+1,qv[s]);if(F[s])g.add(N,s,INF);if(Z[s])g.add(s,N+1,INF);}
 for(auto [s,t]:basearcs)g.add(s,t,INF);
 for(int s:seeds)for(int t=0;t<N;t++)if((s|t)!=t)g.add(t,s|t,INF);
 if(g.flow(N,N+1)-NEG<0)throw runtime_error("leaf bound is negative");
 leaves++;return 0;
}
int main(int argc,char**argv){ios::sync_with_stdio(false);if(!(cin>>n)||n<1||n>9){cerr<<"n must be between 1 and 9\n";return 3;}N=1<<n;vector<int>w(n);int W=0;for(int&i:w){if(!(cin>>i)||i<0||i>1000){cerr<<"invalid weight\n";return 3;}W+=i;}if(W==0){cerr<<"weights must be nonzero\n";return 3;}int m;if(!(cin>>m)||m<0||m>N){cerr<<"invalid generator count\n";return 3;}A.resize(m);for(int&a:A){if(!(cin>>a)||a<0||a>=N){cerr<<"invalid generator\n";return 3;}}bool verifying=argc>1 && string(argv[1])=="verify";if(!verifying&&argc>1)limitsec=stod(argv[1]);if(!verifying&&argc>2){proofout.open(argv[2]);if(!proofout){cerr<<"cannot open proof file\n";return 3;}}
 AC={0};for(int a:A){vector<int>add;for(int s:AC)add.push_back(s|a);AC.insert(AC.end(),add.begin(),add.end());sort(AC.begin(),AC.end());AC.erase(unique(AC.begin(),AC.end()),AC.end());}
 qv.resize(N);INF=1;NEG=0;
 for(int s=0;s<N;s++){int v=-W;for(int i=0;i<n;i++)if(s>>i&1)v+=2*w[i];qv[s]=v;INF+=abs(v);if(v<0)NEG-=v;}
 set<pair<int,int>>E;for(int s=0;s<N;s++)for(int a:A)if((s|a)!=s)E.emplace(s,s|a);basearcs.assign(E.begin(),E.end());
 
 vector<int> pp(n),used(n);set<int> afam(A.begin(),A.end());
 function<void(int)> gen=[&](int d){if(d<n){for(int j=0;j<n;j++)if(!used[j]&&w[d]==w[j]){pp[d]=j;used[j]=1;gen(d+1);used[j]=0;}return;}vector<int> p(N);for(int s=0;s<N;s++){int t=0;for(int i=0;i<n;i++)if(s>>i&1)t|=1<<pp[i];p[s]=t;}for(int a:A)if(!afam.count(p[a]))return;automaps.push_back(move(p));};gen(0);
 cerr<<"weighted automorphisms "<<automaps.size()<<"\n";
 started=chrono::steady_clock::now();int r;try{if(verifying){if(argc!=3)throw runtime_error("verify requires a certificate path");ifstream in(argv[2]);if(!in)throw runtime_error("cannot open certificate");r=replay(in,Bits(),Bits(),0);string extra;if(in>>extra)throw runtime_error("trailing certificate data");}else r=search(Bits(),Bits(),0);}catch(exception const&e){cerr<<e.what()<<"\n";return 3;}double secs=chrono::duration<double>(chrono::steady_clock::now()-started).count();cout<<"status "<<r<<" nodes "<<nodes<<" leaves "<<leaves<<" conflicts "<<conflicts<<" depth "<<maxdepth<<" seconds "<<secs<<"\n";
 if(r==1){int val=0;for(int s:counterex){val+=qv[s];cout<<s<<' ';}cout<<"\nshare "<<val<<"\n";}
 return r;
}
