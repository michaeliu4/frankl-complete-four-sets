#include <bits/stdc++.h>
using namespace std;using U=uint64_t;vector<int>E;int ix[128];unordered_map<U,U>memo;
U canonical(U fam){auto it=memo.find(fam);if(it!=memo.end())return it->second;vector<int>A;int d[7]={};for(int j=0;j<35;j++)if(fam>>j&1){A.push_back(E[j]);for(int i=0;i<7;i++)d[i]+=(E[j]>>i)&1;}
 vector<pair<int,int>> vv;for(int i=0;i<7;i++)vv.push_back({d[i],i});sort(vv.begin(),vv.end());vector<vector<int>>gr;vector<int>st;for(int i=0;i<7;){int j=i;vector<int>g;while(j<7&&vv[j].first==vv[i].first)g.push_back(vv[j++].second);sort(g.begin(),g.end());st.push_back(i);gr.push_back(g);i=j;}int p[7];U best=~U(0);
 function<void(int)>go=[&](int k){if(k<(int)gr.size()){auto g=gr[k];do{for(int j=0;j<(int)g.size();j++)p[g[j]]=st[k]+j;go(k+1);}while(next_permutation(g.begin(),g.end()));return;}U v=0;for(int a:A){int b=0;for(int i=0;i<7;i++)if(a>>i&1)b|=1<<p[i];v|=U(1)<<ix[b];}best=min(best,v);};go(0);memo.emplace(fam,best);return best;}
int main(int argc,char**argv){for(int a=0;a<128;a++)if(__builtin_popcount((unsigned)a)==4){ix[a]=E.size();E.push_back(a);}if(argc>1&&string(argv[1])=="canon"){int k;while(cin>>k){U v=0;for(int i=0;i<k;i++){int a;cin>>a;v|=U(1)<<ix[a];}cout<<canonical(v)<<"\n";}return 0;}
 unordered_set<U>prev;U p;while(cin>>p)prev.insert(p);unordered_set<U>candidates;long long augmentations=0;for(U f:prev)for(int j=0;j<35;j++)if(!(f>>j&1)){++augmentations;candidates.insert(canonical(f|(U(1)<<j)));}
 vector<U>out;long long pruned=0;for(U f:candidates){bool ok=true;for(int j=0;j<35;j++)if((f>>j&1)&&!prev.count(canonical(f^(U(1)<<j)))){ok=false;break;}if(ok)out.push_back(f);else++pruned;}
 sort(out.begin(),out.end());for(U f:out){cout<<f;for(int j=0;j<35;j++)if(f>>j&1)cout<<" "<<E[j];cout<<"\n";}cerr<<"previous "<<prev.size()<<" augmentations "<<augmentations<<" distinct "<<candidates.size()<<" pruned "<<pruned<<" candidates "<<out.size()<<" canonical_cache "<<memo.size()<<"\n";
}
