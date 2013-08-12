#include <iostream>
#include <cstdlib>

#include <string>
#include <sstream>
#include <vector>
#include <queue>
#include <set>
#include <map>
#include <iostream>
#include <fstream>
#include <fstream>
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <cassert>
#include <cstring>
#include "sys/time.h"
using namespace std;
#define ITER(l,i) for(typeof(l.begin()) i=l.begin();i!=l.end();i++)
#define HERE (cerr << "LINE: " << __LINE__ << endl)

typedef long long ll_t;
typedef unsigned long long ull_t;

struct timeval timer_begin, timer_end;

#ifdef LOCAL
#define msg(x) (x)
#else
#define msg(x)
#endif

inline void timer_start() 
{     
  gettimeofday(&timer_begin, NULL);    
}     
inline double timer_now() 
{         
  gettimeofday(&timer_end, NULL);         
  return timer_end.tv_sec - timer_begin.tv_sec +
    (timer_end.tv_usec - timer_begin.tv_usec)/1000000.0;     
}

inline unsigned long xor128(){
  static unsigned long x=123456789,y=362436069,z=521288629,w=88675123;
  unsigned long t;
  t=(x^(x<<11));x=y;y=z;z=w; return( w=(w^(w>>19))^(t^(t>>8)) );
}
template<typename T> void shuffle(vector<T>& v) {
  int sz = v.size();
  for (int i=0; i<sz; i++) 
    swap(v[i], v[xor128()%(sz-i)]);
}
template<typename T> void sort_uniq(vector<T>& v) {
  if (v.size() <= 1)
    return;
  sort(v.begin(), v.end());
  int j=0;
  for (int i=0; i<v.size(); i++)
    if (v[i] != v[j]) {
      j++;
      v[j] = v[i];
    }
  v.resize(j+1);
}

template<typename T> ostream& operator<<(ostream& os, const vector<T>& v) {
  os << "[ ";
  for(typename vector<T>::const_iterator it=v.begin(); it!=v.end(); ++it)
    os << '\"' << *it << '\"' << (it+1==v.end() ? "" : ", "); os << " ]"; 
  return os; 
}
template<typename T> ostream& operator<<(ostream& os, const set<T>& v) {
  os << "{ ";
  for(typename set<T>::const_iterator it=v.begin(); it!=v.end(); ++it) {
    if (it != v.begin())
      os << ", ";
    os << *it; 
  }
  os << " }"; 
  return os; 
}
template<typename T1,typename T2> ostream& operator<<(ostream& os, const pair<T1,T2>& v) {
  os << "[ " << v.first << ", " << v.second << "]";
  return os; 
}

struct uf_t {
  vector <int> parent;

  void add(int elm) {
    if (elm >= parent.size()) 
      parent.resize(elm+1, -1);
  }

  void merge(int a,int b) {
    add(a);
    add(b);

    int ia = a;
    int ib = b;

    if ((ia^ib)&1) swap(ia, ib);  // ok?
      
    int ra = root(ia);
    int rb = root(ib);

    if (ra != rb) {
      parent[ra] += parent[rb];
      parent[rb] = ra;
    }
  }

  int id(int elm) {
    return root(elm);
  }

  int root(int ia) {
    add(ia);
    return (parent[ia] < 0) ? ia : (parent[ia] = root(parent[ia]));
  }
};

typedef char sym_t;
const sym_t SYM_0 = 0;
const sym_t SYM_1 = 1;
const sym_t SYM_X = 2;
const sym_t SYM_Y = 3;
const sym_t SYM_Z = 4;

const sym_t SYM_NOT   = 0x10;
const sym_t SYM_SHL1  = 0x11;
const sym_t SYM_SHR1  = 0x12;
const sym_t SYM_SHR4  = 0x13;
const sym_t SYM_SHR16 = 0x14;

const sym_t SYM_AND  = 0x20;
const sym_t SYM_OR   = 0x21;
const sym_t SYM_XOR  = 0x22;
const sym_t SYM_PLUS = 0x23;

const sym_t SYM_IF0  = 0x30;
const sym_t SYM_FOLD = 0x31;

inline bool valid_sym(sym_t x) { return (x>=2); } // loose check

int arity(sym_t sym) { return (sym>>4); }

map<ull_t, int> known_constant;
map<ull_t, int> known_expr;
int gen_constant;
struct node_t {
  sym_t op;
  int id1, id2, id3;
  bool constant;
  bool fold_used;
  ull_t val;
  string s;
};
ostream& operator<<(ostream& os,node_t node) {
  if (node.constant)
    os << "[" << node.op << ", " << node.id1 << ", " << node.id2 << ", " << node.id3 << "] => " << node.val;
  else
    os << "[" << node.op << ", " << node.id1 << ", " << node.id2 << ", " << node.id3 << "]";
  return os;
};

vector<node_t> pool;
map<string, sym_t> str2sym;
map<sym_t, string> sym2str;

ull_t y, z;
bool inside_fold;
bool valid_eval;

ull_t eval_node(int id, ull_t x) {
  const node_t& node = pool[id];  

  if (node.constant)
    return node.val;

  switch (node.op) {
  case SYM_0: return 0;
  case SYM_1: return 1;
  case SYM_X: return x;
  case SYM_Y: 
    if (!inside_fold)
      valid_eval = false;
    return y;
  case SYM_Z: 
    if (!inside_fold)
      valid_eval = false;
    return z;

  case SYM_NOT: return ~eval_node(node.id1, x);
  case SYM_SHL1: return (eval_node(node.id1, x) << 1);
  case SYM_SHR1: return (eval_node(node.id1, x) >> 1);
  case SYM_SHR4: return (eval_node(node.id1, x) >> 4);
  case SYM_SHR16: return (eval_node(node.id1, x) >> 16);

  case SYM_AND: return (eval_node(node.id1, x) & eval_node(node.id2, x));
    
  case SYM_OR: return (eval_node(node.id1, x) | eval_node(node.id2, x));
  case SYM_XOR: return (eval_node(node.id1, x) ^ eval_node(node.id2, x));
  case SYM_PLUS: return (eval_node(node.id1, x) + eval_node(node.id2, x));

  case SYM_IF0: 
    return (eval_node(node.id1, x) == 0) ? 
      eval_node(node.id2, x) : eval_node(node.id3, x);
    break;
  case SYM_FOLD: 
    {
      ull_t e0 = eval_node(node.id1, x);
      ull_t e1 = eval_node(node.id2, x);
      inside_fold = true;
      for (int i=0; i<8; i++) {
	y = e0 & 0xff;
	z = e1;
	e1 = eval_node(node.id3, x);
	e0 >>= 8;
      }
      inside_fold = false;
      return e1;
    }

  default:
    cerr << "ER: " << (int)node.op << endl;
    assert(false);
  }
}

ull_t eval_node0(int id, ull_t x) {
  inside_fold = false;
  valid_eval = true;
  return eval_node(id, x);
}

int new_node(sym_t op,int id1=-1,int id2=-1,int id3=-1) {
  assert(arity(op) < 1 || id1 >= 0);
  assert(arity(op) < 2 || id2 >= 0);
  assert(arity(op) < 3 || id3 >= 0);

  if (arity(op) == 2 && id1 > id2)
    swap(id1, id2);

#if 1
  if (op == SYM_IF0) {
    if (id1 == SYM_0) // (if0 0 S T) => S
      return id2;
    if (id1 == SYM_1) // (if0 1 S T) => T
      return id3;
    if (id2 == id3)  // (if0 S T T) => T
      return id2;
    if (id2 == 0 && id1 == id3) // (if0 S 0 S) => S
      return id3;
    if (id1 == id2 && id3 == 0) // (if0 S S 0) => 0
      return SYM_0;
    if (pool[id1].constant == true) {
      if (pool[id1].val == 0)
	return id2;
      else
	return id3;
    }
  } else if (op == SYM_AND) {
    if (id1 == SYM_0 || id2 == SYM_0) // (and 0 S) == (and S 0) == 0
      return SYM_0;
    if (id1 == id2) // (and S S) => S
      return id1;
    if (pool[id1].op == SYM_AND && 
	(pool[id1].id1 == id2 || pool[id1].id2 == id2)) // (and (and S T) S) => (and S T)
      return id1;
    if (pool[id2].op == SYM_AND) {
      if (pool[id2].id1 == id1 || pool[id2].id2 == id1)
	return id2;
    }
  } else if (op == SYM_XOR) {
    if (id1 == SYM_0)
      return id2;
    if (id2 == SYM_0)
      return id1;
    if (id1 == id2)
      return SYM_0;
    if (pool[id1].op == SYM_XOR && pool[id1].id1 == id2) // (xor (xor S T) S) => T
      return pool[id1].id2;
  } else if (op == SYM_OR) {
    if (id1 == SYM_0)
      return id2;
    if (id2 == SYM_0)
      return id1;
    if (id1 == id2)
      return id1;
    if (pool[id2].op == SYM_OR) {
      if (pool[id2].id1 == id1 || pool[id2].id2 == id1)
	return id2;
    }
  } else if (op == SYM_PLUS) {
    if (id1 == SYM_0)
      return id2;
    if (id2 == SYM_0)
      return id1;
  } else if (op == SYM_NOT) {
    if (pool[id1].op == SYM_NOT)
      return pool[id1].id1;
  } else if (op == SYM_SHL1) {
    if (id1 == SYM_0)
      return SYM_0;
  } else if (op == SYM_SHR1) {
    if (id1 == SYM_0 || id1 == SYM_1)
      return SYM_0;
    if (pool[id1].op == SYM_SHR4 || pool[id1].op == SYM_SHR16)
      return -1;
  } else if (op == SYM_SHR4) {
    if (id1 == SYM_0 || id1 == SYM_1)
      return SYM_0;
    if (pool[id1].op == SYM_SHR16)
      return -1;
  } else if (op == SYM_SHR16) {
    if (id1 == SYM_0 || id1 == SYM_1)
      return SYM_0;
    if (pool[id1].op == SYM_SHR16 &&
	pool[pool[id1].id1].op == SYM_SHR16 &&
	pool[pool[pool[id1].id1].id1].op == SYM_SHR16) {
      return SYM_0;
    }
  } else if (op == SYM_FOLD) {
    if (pool[id1].fold_used || pool[id2].fold_used || pool[id3].fold_used) 
      return -1;

    if (pool[id3].constant)
      return id3;
    if (id3 == SYM_X)
      return SYM_X;
  }
#endif
  //pool.emplace_back(op, id1, id2, id3);
  pool.push_back({op, id1, id2, id3, false, false});
  int id = pool.size() - 1;
  node_t& node = pool.back();
  node.fold_used = (op == SYM_FOLD ||
		    (id1 >= 0 && pool[id1].fold_used) ||
		    (id2 >= 0 && pool[id2].fold_used) ||
		    (id3 >= 0 && pool[id3].fold_used));

  bool dup = false;

  if (node.op == SYM_0 || node.op == SYM_1) {
    node.constant = true;
    node.val = node.op;
    return id;
  } else if (arity(node.op) == 1 && pool[node.id1].constant) {

    node.val = eval_node0(id, 0); // dummy arg
    node.constant = true;
  } else if (arity(node.op) == 2 && 
	pool[node.id1].constant &&
	pool[node.id2].constant) {

    node.val = eval_node0(id, 0); // dummy arg
    node.constant = true;
  }

  if (node.constant) {
    if (node.val == 0) {
      pool.pop_back();
      return SYM_0;
    } else if (node.val == 1) {
      pool.pop_back();
      return SYM_1;
    } else if (known_constant.count(node.val)) {
      id = known_constant[node.val];
      pool.pop_back();
      return id;
    }
    known_constant[node.val] = id;
    gen_constant++;
  }

  if (false) {
    for (int i=0; i<id && i<1000; i++)
      if (node.op == pool[i].op &&
	  node.id1 == pool[i].id1 &&
	  node.id2 == pool[i].id2 &&
	  node.id3 == pool[i].id3) {
	pool.pop_back();
	return i;
      }
  }

  return id;
}

const string& node_string(int id) {
  node_t& node = pool[id];
  if (!node.s.empty())
    return node.s;

  sym_t op = node.op;
  if (arity(op) == 0) {
    node.s = sym2str[op];
  } else if (arity(op) == 1) {
    node.s = "[" + sym2str[op] + ", " + node_string(node.id1) + "]";
  } else if (arity(op) == 2) {
    node.s = "[" + 
      sym2str[op] + ", " + 
      node_string(node.id1) + ", " +
      node_string(node.id2) + "]";
  } else if (op == SYM_IF0) {
    node.s = "[" + 
      sym2str[op] + ", " + 
      node_string(node.id1) + ", " +
      node_string(node.id2) + ", " +
      node_string(node.id3) + "]";
  } else if (op == SYM_FOLD) {
    node.s = "[" + 
      sym2str[op] + ", " + 
      node_string(node.id1) + ", " +
      node_string(node.id2) + ", :y, :z, " +
      node_string(node.id3) + "]";
  } else {
    node.s = "???";
  }
  return node.s;
}

struct spec_t {
  int size;
  vector<sym_t> ops;
  bool tfold;
  bool fold;
  bool bonus;
};

spec_t parse_spec(string s) {
  stringstream ss(s);

  string op;

  bool fold = false;
  bool tfold = false;
  bool bonus = false;
  vector<sym_t> syms;

  int n;
  ss >> n;
  cerr << n << endl;
  while (!ss.eof()) {
    ss >> op;

    if (op == ":tfold") {
      tfold = true;
      fold = true;
    } else if (op == ":bonus") {
      bonus = true;
    } else {
      sym_t sym = str2sym[op];

      if (valid_sym(sym)) {
	if (sym == SYM_FOLD)
	  fold = true;
	syms.push_back(sym);
      } else {
	cerr << "*** Unknown operator " << op << "  : skip." << endl;
      }
    }
  }

  return spec_t({n, syms, tfold, fold, bonus});
}

#if 0
vector<int> generate_candidates(int size,
			 const vector<sym_t>& ops,
			 bool tfold,
				bool fold) {}
#endif
vector<int> generate_candidates(spec_t& spec) {
  int size = spec.size;
  const vector<sym_t>& ops = spec.ops;
  bool tfold = spec.tfold;
  bool fold = spec.fold;
  bool bonus = spec.bonus;

  vector<vector<int>> memo(2);

  memo[1].push_back(new_node(SYM_0));
  memo[1].push_back(new_node(SYM_1));
  memo[1].push_back(new_node(SYM_X));
  if (fold) {
    memo[1].push_back(new_node(SYM_Y));    
    memo[1].push_back(new_node(SYM_Z));
  }

  vector<int> cur;
  for (int n=2; n<size; n++) {
    if (tfold && n == size-4)
      break;

    cur.clear();
    for (int i=0; i<ops.size(); i++) {
      sym_t op = ops[i];
      if (bonus && n == size-1 && op != SYM_IF0)
	continue;
      
      switch (arity(op)) {
      case 1:
	for (int j=0; j<memo[n-1].size(); j++) {
	  int id = new_node(op, memo[n-1][j]);
	  if (id >= 0)
	    cur.push_back(id);
	}

	break;
      case 2:
	for (int sz1=1; 1+sz1+1<=n; sz1++) {
	  int sz2 = n-(1+sz1);
	  if (sz2 < sz1)
	    break;

	  for (int j=0; j<memo[sz1].size(); j++)
	    for (int k=((sz1 == sz2) ? j : 0); k<memo[sz2].size(); k++)
	      cur.push_back(new_node(op, memo[sz1][j], memo[sz2][k]));
	}
	break;

      case 3:
	if (op == SYM_IF0) {
	  int sz = 1;
	  for (int sz1=1; sz+sz1+1+1<=n; sz1++) 
	    for (int sz2=1; sz+sz1+sz2+1<=n; sz2++) {
	      int sz3 = n-(sz+sz1+sz2);

	      for (int j=0; j<memo[sz1].size(); j++)
		for (int k=0; k<memo[sz2].size(); k++)
		  for (int m=0; m<memo[sz3].size(); m++)
		    cur.push_back(new_node(op, 
					   memo[sz1][j], 
					   memo[sz2][k], 
					   memo[sz3][m]));
	    }
	} else if (op == SYM_FOLD && n == size-1) {
	  int sz = 1;
	  for (int sz1=1; sz+sz1+1+1<=n; sz1++) 
	    for (int sz2=1; sz+sz1+sz2+1<=n; sz2++) {
	      int sz3 = n-(sz+sz1+sz2);

	      for (int j=0; j<memo[sz1].size(); j++)
		for (int k=0; k<memo[sz2].size(); k++)
		  for (int m=0; m<memo[sz3].size(); m++) {
		    int id = new_node(op, 
				      memo[sz1][j], 
				      memo[sz2][k], 
				      memo[sz3][m]);
		    if (id >=0)
		      cur.push_back(id);
		  }
	    }
	  //assert(op != SYM_FOLD);
	  // do nothing
	}
	break;
      default:
	assert(arity(op) == 1);
      }
    }

    sort_uniq(cur);

    cerr << "N: " << n << " " << cur.size() << endl;
#if 0
    if (cur.size() < 100) {
      for (int i=0; i<cur.size(); i++) 
	cerr << "#" << i 
	     << " " << cur[i]
	     << " " << node_string(cur[i]) << endl;
    }
#endif
    if (n > 20)
      break;
    memo.push_back(cur);
  }

  if (tfold) {
    cur.clear();
    cerr << memo.size() << endl;
    for (int j=0; j<memo[size-5].size(); j++)
      cur.push_back(new_node(SYM_FOLD, SYM_X, 0, memo[size-5][j]));
    return cur;
  }

  if (!tfold && fold) {
    cur.clear();
    for (int j=0; j<memo.back().size(); j++)
      if (pool[memo.back()[j]].fold_used)
	cur.push_back(memo.back()[j]);
    return cur;
  }

  return memo.back();
}

int main()
{
  str2sym = {
    {"0", SYM_0},
    {"1", SYM_1},
    {":x", SYM_X},
    {":y", SYM_Y},
    {":z", SYM_Z},

    {":not" , SYM_NOT},
    {":shl1", SYM_SHL1},
    {":shr1", SYM_SHR1},
    {":shr4", SYM_SHR4},
    {":shr16", SYM_SHR16},

    {":and" , SYM_AND},
    {":or"  , SYM_OR},
    {":xor" , SYM_XOR},
    {":plus", SYM_PLUS},

    {":if0" , SYM_IF0},
    {":fold", SYM_FOLD},
  };
  ITER(str2sym, it) {
    sym2str[it->second] = it->first;
  }

  string l;
  getline(cin, l);
  auto spec = parse_spec(l);

  auto nodes0 = generate_candidates(spec);
  auto nodes = nodes0;
  cout << nodes.size() << endl;
  vector<int> nxt;

  cerr << "size: " << nodes.size() << endl;
  cerr << "known_constant: " << known_constant.size() << endl;
  cerr << "gen_constant: " << gen_constant << endl;

  while (true) {
    getline(cin, l);
    if (l == "quit" || cin.eof())
      break;

    if (l == "get") {
      for (int i=0; i<nodes.size(); i++) {
	//cout << node_string(nodes[i]) << " " << nodes[i] << " " << pool[nodes[i]] << endl;
	if (pool[nodes[i]].constant)
	  cout << node_string(nodes[i]) << " # " << pool[nodes[i]].val << endl;
	else
	  cout << node_string(nodes[i]) << endl;
      }
      break;
    }

    ull_t arg, expected;
    stringstream ss(l);
    ss >> arg >> expected;

    int sz1 = nodes.size();
    nxt.clear();
    for (int i=0; i<nodes.size(); i++) {
      if (eval_node0(nodes[i], arg) == expected && valid_eval)
	nxt.push_back(nodes[i]);
    }
    int sz2 = nxt.size();
#if 0
    for (int i=(int)nodes.size()-1; i>=0; i--) {
      if (eval_node0(nodes[i], arg) != expected) {
	swap(nodes[i], nodes.back());
	nodes.pop_back();
      }
    }
    int sz2 = nodes.size();
#endif
    cout << sz2 << endl;

    fprintf(stderr, "  f(0x%016llX) == 0x%016llX : %d => %d \n", arg, expected, sz1, sz2);
    fflush(stderr);

    nodes = nxt;
  }
}
