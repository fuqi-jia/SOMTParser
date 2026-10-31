#include "somtparser/lowering/z3_finite_set_lowering.h"
#include "somtparser/core/checked_integer.h"
#include <algorithm>
#include <cctype>
#include <cstdint>
#include <iterator>
#include <limits>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace SOMTParser::Lower {
namespace {
struct Token { std::string_view text; std::size_t mate=0; bool list=false; bool quoted_symbol=false; bool string_literal=false; };
std::vector<Token> tokenize(const std::string& input) {
    std::vector<Token> ts; std::vector<std::size_t> stack;
    for(std::size_t i=0;i<input.size();) {
        unsigned char c=static_cast<unsigned char>(input[i]);
        if(std::isspace(c)) { ++i; continue; }
        if(input[i]==';') { while(i<input.size() && input[i]!='\n') ++i; continue; }
        if(input[i]=='(') { std::size_t k=ts.size(); ts.push_back({std::string_view(input.data()+i,1),0,true}); stack.push_back(k); ++i; continue; }
        if(input[i]==')') { if(stack.empty()) throw std::runtime_error("Z3 set lowering: unmatched close parenthesis"); std::size_t k=ts.size(); ts.push_back({std::string_view(input.data()+i,1),0,true}); ts[k].mate=stack.back(); ts[stack.back()].mate=k; stack.pop_back(); ++i; continue; }
        std::size_t b=i;
        const bool quoted_symbol=input[i]=='|', string_literal=input[i]=='"';
        if(quoted_symbol || string_literal) { const char q=input[i++]; while(i<input.size()) { char x=input[i++]; if(x==q) { if(q=='"' && i<input.size() && input[i]=='"') { ++i; continue; } break; } } }
        else while(i<input.size() && !std::isspace(static_cast<unsigned char>(input[i])) && input[i]!='(' && input[i]!=')' && input[i]!=';') ++i;
        ts.push_back({std::string_view(input.data()+b,i-b),0,false,quoted_symbol,string_literal});
    }
    if(!stack.empty()) throw std::runtime_error("Z3 set lowering: unterminated list");
    return ts;
}
using Range=std::pair<std::size_t,std::size_t>; // [begin,end)
std::size_t next(const std::vector<Token>& t,std::size_t i) { return t[i].list && t[i].text=="(" ? t[i].mate+1 : i+1; }
std::string_view symbolIdentity(const Token& token) {
    if(token.quoted_symbol && token.text.size()>=2) return token.text.substr(1,token.text.size()-2);
    return token.text;
}
bool is(const std::vector<Token>& t,std::size_t i,std::string_view v) {
    return i<t.size() && !t[i].string_literal && symbolIdentity(t[i])==v;
}
bool keyword(const std::vector<Token>& t,std::size_t i,std::string_view v) {
    return i<t.size() && !t[i].quoted_symbol && !t[i].string_literal && t[i].text==v;
}
bool listHead(const std::vector<Token>& t,std::size_t i,std::string_view h) {
    if(i>=t.size() || t[i].text!="(") return false;
    // Reserved syntax and quoted function names occupy different roles.
    // Ordinary symbols still compare by identity, e.g. u and |u|.
    if(h=="forall" || h=="exists" || h=="lambda" || h=="let" ||
       h=="as" || h=="match" || h=="par") return keyword(t,i+1,h);
    return is(t,i+1,h);
}
void appendRange(const std::vector<Token>& t,Range r,std::string& out) { for(std::size_t i=r.first;i<r.second;++i) { if(i>r.first) out.push_back(' '); out.append(t[i].text.data(),t[i].text.size()); } }
std::string canonical(const std::vector<Token>& t,Range r) { std::string s; appendRange(t,r,s); return s; }
std::string proofKey(const std::vector<Token>& t,Range r) {
    std::string key;
    for(std::size_t i=r.first;i<r.second;++i) {
        if(t[i].list) { key+=t[i].text; key.push_back(';'); continue; }
        std::string_view identity=symbolIdentity(t[i]);
        char category='S';
        if(t[i].string_literal) category='T';
        else if(!t[i].quoted_symbol && !t[i].text.empty() &&
                (std::isdigit(static_cast<unsigned char>(t[i].text.front())) || t[i].text.front()=='#')) category='L';
        key.push_back(category); key+=std::to_string(identity.size()); key.push_back(':'); key.append(identity); key.push_back(';');
    }
    return key;
}
bool parseInt(const std::vector<Token>& t,Range r,std::int64_t& n) {
    if(r.second==r.first+1) { try { std::string s(t[r.first].text); std::size_t used=0; long long x=std::stoll(s,&used); if(used==s.size()) { n=x; return true; } } catch(...){} }
    if(r.second==r.first+4 && is(t,r.first,"(") && is(t,r.first+1,"-") && t[r.first+2].text.size() && is(t,r.first+3,")")) { try { std::string s(t[r.first+2].text); std::size_t used=0; long long x=std::stoll(s,&used); if(used==s.size() && x!=std::numeric_limits<long long>::min()) { n=-x; return true; } } catch(...){} }
    return false;
}
struct Bounds { std::int64_t lo,hi; };
using BoundMap=std::unordered_map<std::string,Bounds>;
struct IntInterval { std::int64_t lo,hi; bool has_lo=false,has_hi=false; };
using IntBoundMap=std::unordered_map<std::string,IntInterval>;
void flattenAnd(const std::vector<Token>& t,Range r,std::vector<Range>& out) {
    std::vector<Range> pending{r};
    while(!pending.empty()) {
        const auto term=pending.back(); pending.pop_back();
        if(listHead(t,term.first,"and") && t[term.first].mate+1==term.second) {
            const auto before=pending.size();
            for(auto p=term.first+2;p<t[term.first].mate;p=next(t,p)) pending.emplace_back(p,next(t,p));
            std::reverse(pending.begin()+static_cast<std::ptrdiff_t>(before),pending.end());
        } else out.push_back(term);
    }
}
void addBound(const std::vector<Token>& t,Range assert_r,BoundMap& bounds) {
    if(!listHead(t,assert_r.first,"assert") || t[assert_r.first].mate+1!=assert_r.second) return;
    std::size_t q=assert_r.first+2;
    if(!listHead(t,q,"forall")) return;
    const auto qclose=t[q].mate;
    std::size_t bindlist=q+2; if(!is(t,bindlist,"(")) return;
    std::size_t bind=bindlist+1; if(!is(t,bind,"(") || next(t,bind)!=t[bindlist].mate || t[bind].mate!=bind+3 || !is(t,bind+2,"Int")) return;
    const std::string var(symbolIdentity(t[bind+1])); std::size_t body=t[bindlist].mate+1;
    if(!listHead(t,body,"=>") || t[body].mate+1!=qclose) return;
    std::size_t ant=body+2,cons=next(t,ant);
    if(!listHead(t,ant,"set.member") || t[ant].mate+1!=cons || !is(t,ant+2,var)) return;
    std::size_t setpos=next(t,ant+2),setend=next(t,setpos);
    if(setend!=t[ant].mate) return;
    // A reference to the forall binder inside the set operand would be captured;
    // it is a diagonal restriction, not an unconditional carrier bound.
    // SMT-LIB simple and quoted spellings denote the same symbol. Compare
    // normalized identities here: otherwise `|u|` can evade the check for a
    // binder named `u`, and a diagonal membership condition can be mistaken
    // for a global finite-carrier proof.
    const auto binder_identity=symbolIdentity(t[bind+1]);
    for(std::size_t i=setpos;i<setend;++i)
        if(!t[i].list && !t[i].string_literal && symbolIdentity(t[i])==binder_identity) return;
    std::vector<Range> tests; flattenAnd(t,{cons,t[body].mate},tests);
    bool has_lo=false,has_hi=false; std::int64_t lo=std::numeric_limits<std::int64_t>::min(),hi=std::numeric_limits<std::int64_t>::max();
    for(auto c:tests) {
        if(!listHead(t,c.first,"<=") && !listHead(t,c.first,"<") && !listHead(t,c.first,">=") && !listHead(t,c.first,">")) continue;
        std::size_t a=c.first+2,b=next(t,a); if(next(t,b)!=t[c.first].mate) continue;
        const auto op=t[c.first+1].text; std::int64_t n=0;
        if((op==">="||op==">") && is(t,a,var) && parseInt(t,{b,t[c.first].mate},n)) { if(op==">" && n<std::numeric_limits<std::int64_t>::max()) ++n; else if(op==">") continue; lo=std::max(lo,n); has_lo=true; }
        else if((op=="<="||op=="<") && is(t,a,var) && parseInt(t,{b,t[c.first].mate},n)) { if(op=="<" && n>std::numeric_limits<std::int64_t>::min()) --n; else if(op=="<") continue; hi=std::min(hi,n); has_hi=true; }
        else if((op=="<="||op=="<") && is(t,b,var) && parseInt(t,{a,b},n)) { if(op=="<" && n<std::numeric_limits<std::int64_t>::max()) ++n; else if(op=="<") continue; lo=std::max(lo,n); has_lo=true; }
        else if((op==">="||op==">") && is(t,b,var) && parseInt(t,{a,b},n)) { if(op==">" && n>std::numeric_limits<std::int64_t>::min()) --n; else if(op==">") continue; hi=std::min(hi,n); has_hi=true; }
    }
    if(!has_lo||!has_hi) return;
    auto key=proofKey(t,{setpos,setend}); auto it=bounds.find(key);
    if(it==bounds.end()) bounds.emplace(std::move(key),Bounds{lo,hi});
    else { it->second.lo=std::max(it->second.lo,lo); it->second.hi=std::min(it->second.hi,hi); }
}
// Read a closed literal carrier without consulting asserted facts. Empty
// carriers use lo > hi, also understood by cardinalityTerm. An interval hull
// is sufficient here: the original sparse-set equality remains in the script,
// and cardinality still tests membership at every candidate in the hull.
bool literalCarrier(const std::vector<Token>& t, Range r, Bounds& carrier) {
    bool empty = true;
    const auto add = [&](std::int64_t value) {
        if (empty) { carrier = {value, value}; empty = false; }
        else { carrier.lo = std::min(carrier.lo, value); carrier.hi = std::max(carrier.hi, value); }
    };
    for (;;) {
        if (r.first >= r.second || !t[r.first].list || t[r.first].mate + 1 != r.second) return false;
        const auto close = t[r.first].mate;
        if (listHead(t, r.first, "as") && is(t, r.first + 2, "set.empty")) {
            const auto sort = r.first + 3;
            if (!listHead(t, sort, "Set") || !is(t, sort + 2, "Int")
                || next(t, sort + 2) != t[sort].mate || next(t, sort) != close) return false;
            if (empty) carrier = {1, 0};
            return true;
        }
        if (listHead(t, r.first, "set.singleton")) {
            const auto value = r.first + 2;
            std::int64_t n;
            if (next(t, value) != close || !parseInt(t, {value, close}, n)) return false;
            add(n); return true;
        }
        if (!listHead(t, r.first, "set.insert")) return false;
        auto value = r.first + 2;
        if (value >= close) return false;
        auto end = next(t, value);
        if (end >= close) return false;
        while (end < close) {
            std::int64_t n;
            if (!parseInt(t, {value, end}, n)) return false;
            add(n); value = end; end = next(t, value);
        }
        // Nested inserts need no recursion, even for large literal sets.
        r = {value, end};
    }
}

bool equalityCarrier(const std::vector<Token>& t, Range r, Bounds& carrier) {
    if (literalCarrier(t, r, carrier)) return true;
    if (!listHead(t, r.first, "set.inter") || t[r.first].mate + 1 != r.second) return false;
    // An intersection is contained in each operand. One closed literal
    // operand therefore suffices; no assertion under a binder is borrowed.
    for (auto p = r.first + 2; p < t[r.first].mate;) {
        const auto end = next(t, p);
        if (literalCarrier(t, {p, end}, carrier)) return true;
        p = end;
    }
    return false;
}

void addEqualityBound(const std::vector<Token>& t, Range r, BoundMap& bounds) {
    if (!listHead(t, r.first, "=") || t[r.first].mate + 1 != r.second) return;
    const auto left = r.first + 2, right = next(t, left), close = t[r.first].mate;
    if (right >= close || next(t, right) != close) return;
    const Range operands[] = {{left, right}, {right, close}};
    for (std::size_t side = 0; side < 2; ++side) {
        Bounds carrier;
        if (!equalityCarrier(t, operands[1 - side], carrier)) continue;
        const auto term = operands[side];
        bool scoped = false;
        for (auto p = term.first; p < term.second; ++p) {
            if (listHead(t, p, "forall") || listHead(t, p, "exists")
                || listHead(t, p, "lambda") || listHead(t, p, "let")
                || listHead(t, p, "match")) { scoped = true; break; }
        }
        if (scoped) continue;
        auto key = proofKey(t, term);
        const auto it = bounds.find(key);
        if (it == bounds.end()) bounds.emplace(std::move(key), carrier);
        else {
            it->second.lo = std::max(it->second.lo, carrier.lo);
            it->second.hi = std::min(it->second.hi, carrier.hi);
        }
    }
}

void findBounds(const std::vector<Token>& t,Range r,BoundMap& b) {
    std::size_t p=r.first;
    while(p<r.second) {
        auto q=next(t,p); if(q<=p||q>r.second) break;
        if(listHead(t,p,"assert")) {
            addBound(t,{p,q},b);
            // Only positive asserted conjuncts constrain the whole script.
            // An equality inside NOT, OR, reification, or a binder cannot
            // establish a global carrier for cardinality or Set lowering.
            std::vector<Range> conjuncts;
            flattenAnd(t,{p+2,t[p].mate},conjuncts);
            for(const auto& conjunct:conjuncts) addEqualityBound(t,conjunct,b);
        }
        p=q;
    }
}
void addIntConstraint(const std::vector<Token>& t,Range term,bool term_is_left,std::string_view op,
                      std::int64_t value,IntBoundMap& bounds) {
    bool has_lo=false,has_hi=false; std::int64_t lo=value,hi=value;
    if(term_is_left) {
        if(op==">=" || op==">") { has_lo=true; if(op==">") { if(value==std::numeric_limits<std::int64_t>::max()) return; ++lo; } }
        else if(op=="<=" || op=="<") { has_hi=true; if(op=="<") { if(value==std::numeric_limits<std::int64_t>::min()) return; --hi; } }
    } else {
        if(op=="<=" || op=="<") { has_lo=true; if(op=="<") { if(value==std::numeric_limits<std::int64_t>::max()) return; ++lo; } }
        else if(op==">=" || op==">") { has_hi=true; if(op==">") { if(value==std::numeric_limits<std::int64_t>::min()) return; --hi; } }
    }
    if(!has_lo && !has_hi) return;
    auto& entry=bounds[proofKey(t,term)];
    if(has_lo) { entry.lo=entry.has_lo?std::max(entry.lo,lo):lo; entry.has_lo=true; }
    if(has_hi) { entry.hi=entry.has_hi?std::min(entry.hi,hi):hi; entry.has_hi=true; }
}
void addIntBoundsFromConjunct(const std::vector<Token>& t,Range conjunct,IntBoundMap& bounds) {
    if(!listHead(t,conjunct.first,"<") && !listHead(t,conjunct.first,"<=") &&
       !listHead(t,conjunct.first,">") && !listHead(t,conjunct.first,">=")) return;
    const auto close=t[conjunct.first].mate;
    const auto op=t[conjunct.first+1].text;
    const std::size_t left=conjunct.first+2,right=next(t,left);
    if(next(t,right)!=close) return;
    std::int64_t value=0;
    if(parseInt(t,{right,close},value)) addIntConstraint(t,{left,right},true,op,value,bounds);
    else if(parseInt(t,{left,right},value)) addIntConstraint(t,{right,close},false,op,value,bounds);
}
void findIntBounds(const std::vector<Token>& t,IntBoundMap& bounds) {
    for(std::size_t p=0;p<t.size();) {
        const auto q=next(t,p); if(q<=p) return;
        if(listHead(t,p,"assert") && t[p].mate+1==q) {
            std::vector<Range> conjuncts; flattenAnd(t,{p+2,t[p].mate},conjuncts);
            for(const auto& c:conjuncts) addIntBoundsFromConjunct(t,c,bounds);
        }
        p=q;
    }
}
bool integerInterval(const std::vector<Token>& t,Range root,const IntBoundMap& known,IntInterval& out) {
    struct Pending { Range term; bool leave; };
    std::vector<Pending> pending{{root,false}};
    std::unordered_map<std::size_t,IntInterval> results;
    while(!pending.empty()) {
        const auto current=pending.back(); pending.pop_back();
        const auto term=current.term;
        const auto found=known.find(proofKey(t,term));
        if(found!=known.end() && found->second.has_lo && found->second.has_hi && found->second.lo<=found->second.hi) {
            results.emplace(term.first,found->second); continue;
        }
        std::int64_t literal=0;
        if(parseInt(t,term,literal)) { results.emplace(term.first,IntInterval{literal,literal,true,true}); continue; }
        if((!listHead(t,term.first,"+") && !listHead(t,term.first,"-") && !listHead(t,term.first,"*"))
           || t[term.first].mate+1!=term.second) return false;
        std::vector<Range> args;
        for(auto p=term.first+2;p<t[term.first].mate;p=next(t,p)) args.emplace_back(p,next(t,p));
        const bool subtraction=is(t,term.first+1,"-");
        if(args.empty() || (subtraction && args.size()>2)) return false;
        if(!current.leave) {
            pending.push_back({term,true});
            for(auto it=args.rbegin();it!=args.rend();++it) pending.push_back({*it,false});
            continue;
        }
        IntInterval acc=results.at(args[0].first);
        if(subtraction && args.size()==1) {
            std::int64_t lo=0,hi=0;
            if(detail::subOverflow(std::int64_t{0},acc.hi,&lo) || detail::subOverflow(std::int64_t{0},acc.lo,&hi)) return false;
            results.emplace(term.first,IntInterval{lo,hi,true,true}); continue;
        }
        for(std::size_t i=1;i<args.size();++i) {
            const auto b=results.at(args[i].first);
            std::int64_t lo=0,hi=0;
            if(is(t,term.first+1,"+")) {
                if(detail::addOverflow(acc.lo,b.lo,&lo) || detail::addOverflow(acc.hi,b.hi,&hi)) return false;
            } else if(subtraction) {
                if(detail::subOverflow(acc.lo,b.hi,&lo) || detail::subOverflow(acc.hi,b.lo,&hi)) return false;
            } else {
                std::int64_t products[4];
                if(detail::mulOverflow(acc.lo,b.lo,&products[0]) || detail::mulOverflow(acc.lo,b.hi,&products[1]) ||
                   detail::mulOverflow(acc.hi,b.lo,&products[2]) || detail::mulOverflow(acc.hi,b.hi,&products[3])) return false;
                const auto limits=std::minmax_element(std::begin(products),std::end(products)); lo=*limits.first; hi=*limits.second;
            }
            acc={lo,hi,true,true};
        }
        results.emplace(term.first,acc);
    }
    out=results.at(root.first); return true;
}
// Resolve only globally unique let aliases whose RHS has a proven integer
// interval. SMT-LIB let is lexical; globally unique names that are not also
// bound by a quantifier/lambda/function formal cannot be shadowed. This covers
// exporter-generated DAG lets while leaving arbitrary local parameters
// unsupported unless independently bounded.
void findUniqueLetIntervals(const std::vector<Token>& t,IntBoundMap& bounds,
                            std::unordered_set<std::string>& safe_names) {
    struct Alias { std::string name; std::size_t name_token; Range rhs; };
    std::vector<Alias> aliases;
    std::unordered_map<std::string,std::size_t> let_counts;
    std::unordered_set<std::string> other_binders;
    std::unordered_set<std::string> declared_names;
    bool unsupported_binder_form=false;
    for(std::size_t p=0;p<t.size();++p) {
        // These binders need dedicated lexical-scope analysis. Conservatively
        // disable all let-alias propagation in scripts containing either form.
        if(listHead(t,p,"match") || listHead(t,p,"define-funs-rec"))
            unsupported_binder_form=true;
        if(listHead(t,p,"declare-const") || listHead(t,p,"declare-fun") ||
           listHead(t,p,"define-fun") || listHead(t,p,"define-fun-rec")) {
            const auto name=p+2;
            if(name<t.size() && !t[name].list && !t[name].string_literal)
                declared_names.emplace(symbolIdentity(t[name]));
        }
        if(listHead(t,p,"let")) {
            const auto binders=p+2;
            if(!is(t,binders,"(")) continue;
            for(std::size_t b=binders+1;b<t[binders].mate;) {
                if(!is(t,b,"(") || b+1>=t[b].mate || t[b+1].list || t[b+1].string_literal) break;
                const auto name=std::string(symbolIdentity(t[b+1]));
                ++let_counts[name];
                aliases.push_back({name,b+1,{next(t,b+1),t[b].mate}});
                b=next(t,b);
            }
        } else if(listHead(t,p,"forall") || listHead(t,p,"exists") || listHead(t,p,"lambda")) {
            const auto binders=p+2;
            if(!is(t,binders,"(")) continue;
            for(std::size_t b=binders+1;b<t[binders].mate;) {
                if(!is(t,b,"(") || b+1>=t[b].mate || t[b+1].list || t[b+1].string_literal) break;
                other_binders.emplace(symbolIdentity(t[b+1]));
                b=next(t,b);
            }
        } else if(listHead(t,p,"define-fun") || listHead(t,p,"define-fun-rec")) {
            const auto binders=next(t,next(t,p+1));
            if(!is(t,binders,"(")) continue;
            for(std::size_t b=binders+1;b<t[binders].mate;) {
                if(!is(t,b,"(") || b+1>=t[b].mate || t[b+1].list || t[b+1].string_literal) break;
                other_binders.emplace(symbolIdentity(t[b+1]));
                b=next(t,b);
            }
        }
    }
    if(unsupported_binder_form) return;
    std::unordered_set<std::string> unique;
    for(const auto& a:aliases)
        if(let_counts[a.name]==1 && !other_binders.count(a.name) &&
           !declared_names.count(a.name)) unique.insert(a.name);
    // Let bindings are simultaneous. To avoid borrowing a sibling or outer
    // local binding's interval under the wrong lexical scope, accept only RHS
    // expressions that contain no spelling used by any let binder. The
    // generated SMT DAG aliases needed for finite array indexes bind direct
    // globally-bounded array selects, so this conservative rule is sufficient.
    for(const auto& a:aliases) {
        if(!unique.count(a.name)) continue;
        bool mentions_let_name=false;
        for(std::size_t i=a.rhs.first;i<a.rhs.second;++i) {
            if(t[i].list || t[i].string_literal) continue;
            const auto referenced=std::string(symbolIdentity(t[i]));
            if(let_counts.count(referenced) || other_binders.count(referenced)) {
                mentions_let_name=true; break;
            }
        }
        if(mentions_let_name) continue;
        IntInterval interval;
        if(integerInterval(t,a.rhs,bounds,interval)) {
            bounds.emplace(proofKey(t,{a.name_token,a.name_token+1}),interval);
            safe_names.insert(a.name);
        }
    }
}

bool containsHead(const std::vector<Token>& t,Range r,std::string_view wanted) {
    for(std::size_t p=r.first;p<r.second;++p) if(listHead(t,p,wanted)) return true;
    return false;
}
bool directSetIntSort(const std::vector<Token>& t,Range sort) {
    if(!listHead(t,sort.first,"Set") || t[sort.first].mate+1!=sort.second) return false;
    const std::size_t element=sort.first+2;
    return is(t,element,"Int") && next(t,element)==t[sort.first].mate;
}
bool directArrayOfSetIntSort(const std::vector<Token>& t,Range sort) {
    if(!listHead(t,sort.first,"Array") || t[sort.first].mate+1!=sort.second) return false;
    const std::size_t index=sort.first+2;
    if(!is(t,index,"Int")) return false;
    const std::size_t element=next(t,index);
    return next(t,element)==t[sort.first].mate && directSetIntSort(t,{element,t[sort.first].mate});
}
bool indexIntervalCovered(const std::map<std::int64_t,Bounds>& cells,std::int64_t lo,std::int64_t hi,Bounds& carrier) {
    if(lo>hi) return false;
    // Unsigned subtraction gives the exact distance for ordered signed endpoints.
    // Compare before adding one, including the full 2^64-element interval.
    const std::uint64_t distance=static_cast<std::uint64_t>(hi)-static_cast<std::uint64_t>(lo);
    if(distance>=cells.size()) return false;
    auto cell=cells.lower_bound(lo);
    std::int64_t expected=lo;
    bool first=true;
    std::size_t count=0;
    std::int64_t carrier_lo=0,carrier_hi=0;
    for(;cell!=cells.end() && cell->first<=hi;++cell) {
        if(cell->first!=expected) return false;
        ++count;
        if(first) { carrier_lo=cell->second.lo; carrier_hi=cell->second.hi; first=false; }
        else { carrier_lo=std::min(carrier_lo,cell->second.lo); carrier_hi=std::max(carrier_hi,cell->second.hi); }
        if(expected==hi) break;
        ++expected;
    }
    if(first || count-1!=distance) return false;
    carrier={carrier_lo,carrier_hi}; return true;
}
bool containsSetSort(const std::vector<Token>& t,Range sort,const std::unordered_set<std::string>& aliases) {
    for(std::size_t p=sort.first;p<sort.second;++p) {
        if(listHead(t,p,"Set")) return true;
        if(!t[p].list && !t[p].string_literal && aliases.count(std::string(symbolIdentity(t[p])))) return true;
    }
    return false;
}
bool hasSetDependentRecursion(const std::vector<Token>& t) {
    struct Definition { Range signature,body; bool recursive,uses_sets=false; };
    std::unordered_map<std::string,Definition> definitions;
    std::unordered_set<std::string> aliases;
    const auto add=[&](std::size_t name,Range signature,Range body,bool recursive) {
        definitions.emplace(std::string(symbolIdentity(t[name])),Definition{signature,body,recursive});
    };
    for(std::size_t p=0;p<t.size();p=next(t,p)) {
        const auto close=t[p].mate;
        if(listHead(t,p,"define-sort")) {
            const auto name=p+2,params=next(t,name),body=next(t,params);
            if(containsSetSort(t,{body,close},aliases)) aliases.emplace(symbolIdentity(t[name]));
        } else if(listHead(t,p,"define-fun") || listHead(t,p,"define-fun-rec")) {
            const auto name=p+2,formals=next(t,name),result=next(t,formals),body=next(t,result);
            add(name,{formals,body},{body,close},listHead(t,p,"define-fun-rec"));
        } else if(listHead(t,p,"declare-fun")) {
            const auto name=p+2,formals=next(t,name);
            add(name,{formals,close},{close,close},false);
        } else if(listHead(t,p,"define-funs-rec")) {
            const auto signatures=p+2,bodies=next(t,signatures);
            auto body=bodies+1;
            for(auto sig=signatures+1;sig<t[signatures].mate;sig=next(t,sig)) {
                const auto name=sig+1,formals=next(t,name),end=next(t,body);
                add(name,{formals,t[sig].mate},{body,end},true);
                body=end;
            }
        }
    }
    for(auto& entry:definitions) {
        auto& def=entry.second;
        def.uses_sets=containsSetSort(t,def.signature,aliases);
        for(auto p=def.body.first;p<def.body.second;++p) {
            const auto symbol=symbolIdentity(t[p]);
            if(!t[p].list && !t[p].string_literal && symbol.substr(0,4)=="set.") def.uses_sets=true;
        }
    }
    // Follow function dependencies, including nonrecursive helpers that capture
    // a global set. Unrelated numeric recursion need not constrain Set values.
    bool changed=true;
    while(changed) {
        changed=false;
        for(auto& entry:definitions) {
            auto& def=entry.second;
            if(def.uses_sets) continue;
            for(auto p=def.body.first;p<def.body.second;++p) {
                if(t[p].list || t[p].string_literal) continue;
                const auto dep=definitions.find(std::string(symbolIdentity(t[p])));
                if(dep!=definitions.end() && dep->second.uses_sets) {
                    def.uses_sets=true; changed=true; break;
                }
            }
        }
    }
    for(const auto& entry:definitions)
        if(entry.second.recursive && entry.second.uses_sets) return true;
    return false;
}
bool hasQuantifiedSet(const std::vector<Token>& t,BoundMap& bounds,bool scoped_context,
                      std::unordered_set<std::string>& safe_let_symbols) {
    bool quantified=hasSetDependentRecursion(t), set_value=false;
    std::unordered_set<std::string> set_aliases, int_set_aliases;
    std::unordered_set<std::string> scoped_symbols;
    IntBoundMap integer_bounds;
    if(!scoped_context) {
        findIntBounds(t,integer_bounds);
        findUniqueLetIntervals(t,integer_bounds,safe_let_symbols);
    }
    std::size_t command_end=0;
    for(std::size_t p=0;p<t.size();++p) {
        const bool top_level=p==command_end;
        if(top_level) command_end=next(t,p);
        if(listHead(t,p,"forall") || listHead(t,p,"exists")) {
            quantified=true;
            const std::size_t binder_list=p+2;
            if(is(t,binder_list,"(")) {
                for(std::size_t b=binder_list+1;b<t[binder_list].mate;) {
                    if(!is(t,b,"(")) return true;
                    const std::size_t name=b+1, sort=next(t,name);
                    if(next(t,sort)!=t[b].mate) return true;
                    if(!t[name].list && !t[name].string_literal) scoped_symbols.insert(std::string(symbolIdentity(t[name])));
                    if(directSetIntSort(t,{sort,t[b].mate}) || containsSetSort(t,{sort,t[b].mate},set_aliases)) return true;
                    b=next(t,b);
                }
            }
        }
        if(listHead(t,p,"let") || listHead(t,p,"lambda")) {
            const std::size_t binders=p+2;
            if(!is(t,binders,"(")) return true;
            for(std::size_t b=binders+1;b<t[binders].mate;) {
                if(!is(t,b,"(") || b+1>=t[b].mate || t[b+1].list || t[b+1].string_literal) return true;
                scoped_symbols.insert(std::string(symbolIdentity(t[b+1])));
                b=next(t,b);
            }
        }
        if(top_level && (listHead(t,p,"define-fun") || listHead(t,p,"define-fun-rec"))) {
            const std::size_t binders=next(t,next(t,p+1));
            if(is(t,binders,"(")) {
                for(std::size_t b=binders+1;b<t[binders].mate;) {
                    if(!is(t,b,"(") || b+1>=t[b].mate || t[b+1].list || t[b+1].string_literal) return true;
                    scoped_symbols.insert(std::string(symbolIdentity(t[b+1])));
                    b=next(t,b);
                }
            }
        }
        if(top_level && listHead(t,p,"define-funs-rec")) {
            const std::size_t signatures=p+2;
            if(!is(t,signatures,"(")) return true;
            for(std::size_t sig=signatures+1;sig<t[signatures].mate;) {
                const std::size_t formals=next(t,sig+1);
                if(!is(t,formals,"(")) return true;
                for(std::size_t b=formals+1;b<t[formals].mate;) {
                    if(!is(t,b,"(") || b+1>=t[b].mate || t[b+1].list || t[b+1].string_literal) return true;
                    scoped_symbols.insert(std::string(symbolIdentity(t[b+1])));
                    b=next(t,b);
                }
                sig=next(t,sig);
            }
        }
        if(listHead(t,p,"Set")) set_value=true;
        if(!t[p].list && !t[p].string_literal) {
            const auto name=symbolIdentity(t[p]);
            if(name.size()>=4 && name.substr(0,4)=="set.") set_value=true;
        }
        if(top_level && listHead(t,p,"define-sort")) {
            const std::size_t name=p+2, params=next(t,name), body=next(t,params);
            if(next(t,body)==t[p].mate) {
                const Range body_range{body,t[p].mate};
                if(directSetIntSort(t,body_range)) { set_aliases.insert(std::string(symbolIdentity(t[name]))); int_set_aliases.insert(std::string(symbolIdentity(t[name]))); }
                else if(containsSetSort(t,body_range,set_aliases)) set_aliases.insert(std::string(symbolIdentity(t[name])));
            }
        }
    }
    if(!set_value) return false;
    // Propagate proved cell carriers to bounded dynamic indexes for QF Set
    // formulas as well. A failed carrier analysis only rejects the script
    // when quantified/recursive Set semantics require that global proof;
    // ordinary QF callers retain the existing local-support fallback.

    // A direct Set Int constant may be encoded by a Boolean array only when an
    // unconditional whole-script carrier proof guarantees it is actually
    // finite. Other Set-bearing declarations (arrays, function parameters or
    // results, datatypes, unresolved aliases) can range over arbitrary arrays.
    std::unordered_set<std::string> bounded_set_arrays;
    std::unordered_set<std::size_t> allowed_array_symbol_tokens;
    for(std::size_t p=0;p<t.size();) {
        const auto q=next(t,p); if(q<=p) return quantified;
        if(listHead(t,p,"declare-const")) {
            const std::size_t name=p+2, sort=next(t,name);
            if(next(t,sort)==t[p].mate && containsSetSort(t,{sort,t[p].mate},set_aliases)) {
                const bool direct_int=directSetIntSort(t,{sort,t[p].mate}) ||
                    (sort+1==t[p].mate && int_set_aliases.count(std::string(symbolIdentity(t[sort]))));
                if(direct_int) {
                    if(!bounds.count(proofKey(t,{name,next(t,name)})) && quantified) return true;
                } else if(directArrayOfSetIntSort(t,{sort,t[p].mate})) {
                    // An array of sets can be represented exactly only for
                    // the concrete cells whose finite carrier is separately
                    // proved. The later scan rejects whole-array, symbolic
                    // cell, store, and any other unproved uses.
                    const auto array_name=std::string(symbolIdentity(t[name]));
                    if(scoped_symbols.count(array_name)) return quantified;
                    bounded_set_arrays.insert(array_name);
                    allowed_array_symbol_tokens.insert(name);
                } else return quantified;
            }
        } else if(listHead(t,p,"declare-fun")) {
            const std::size_t name=p+2, args=next(t,name), result=next(t,args);
            if(next(t,result)==t[p].mate && containsSetSort(t,{args,t[p].mate},set_aliases)) {
                const bool zero_arg=is(t,args,"(") && args+1==t[args].mate;
                const bool direct_int=directSetIntSort(t,{result,t[p].mate}) ||
                    (result+1==t[p].mate && int_set_aliases.count(std::string(symbolIdentity(t[result]))));
                if(!zero_arg) return quantified;
                if(direct_int) {
                    if(!bounds.count(proofKey(t,{name,next(t,name)})) && quantified) return true;
                } else if(directArrayOfSetIntSort(t,{result,t[p].mate})) {
                    const auto array_name=std::string(symbolIdentity(t[name]));
                    if(scoped_symbols.count(array_name)) return quantified;
                    bounded_set_arrays.insert(array_name);
                    allowed_array_symbol_tokens.insert(name);
                } else return quantified;
            }
        } else if(listHead(t,p,"declare-datatype") || listHead(t,p,"declare-datatypes") ||
                  listHead(t,p,"declare-codatatypes")) {
            if(containsSetSort(t,{p,q},set_aliases)) return quantified;
        } else if(listHead(t,p,"define-fun") || listHead(t,p,"define-fun-rec")) {
            const std::size_t name=p+2, binders=next(t,name), result=next(t,binders);
            if(containsSetSort(t,{binders,next(t,result)},set_aliases)) return quantified;
        } else if(listHead(t,p,"define-funs-rec")) {
            const std::size_t signatures=p+2;
            if(!is(t,signatures,"(")) return quantified;
            for(std::size_t s=signatures+1;s<t[signatures].mate;) {
                if(!is(t,s,"(")) return quantified;
                const std::size_t name=s+1, formals=next(t,name), result=next(t,formals);
                if(containsSetSort(t,{formals,next(t,result)},set_aliases)) return quantified;
                s=next(t,s);
            }
        }
        p=q;
    }
    std::unordered_map<std::string,std::map<std::int64_t,Bounds>> bounded_cells;
    for(std::size_t p=0;p<t.size();++p) {
        if(!listHead(t,p,"select")) continue;
        const std::size_t close=t[p].mate,array=p+2;
        if(array>=close || t[array].list || t[array].string_literal) continue;
        const auto array_name=std::string(symbolIdentity(t[array]));
        if(!bounded_set_arrays.count(array_name)) continue;
        const std::size_t index=next(t,array);
        if(next(t,index)!=close) continue;
        std::int64_t fixed_index=0;
        if(parseInt(t,{index,close},fixed_index)) {
            const auto proof=bounds.find(proofKey(t,{p,close+1}));
            if(proof!=bounds.end()) bounded_cells[array_name][fixed_index]=proof->second;
        }
    }
    for(std::size_t p=0;p<t.size();++p) {
        if(listHead(t,p,"select")) {
            const std::size_t close=t[p].mate, array=p+2;
            if(array<close && !t[array].list && !t[array].string_literal &&
               bounded_set_arrays.count(std::string(symbolIdentity(t[array])))) {
                const std::size_t index=next(t,array);
                if(next(t,index)!=close) return quantified;
                const auto key=proofKey(t,{p,close+1});
                if(!bounds.count(key)) {
                    if(scoped_context) return quantified;
                    for(std::size_t i=index;i<close;++i) {
                        if(t[i].list || t[i].string_literal) continue;
                        const auto symbol=std::string(symbolIdentity(t[i]));
                        if(scoped_symbols.count(symbol) && !safe_let_symbols.count(symbol)) return quantified;
                    }
                    IntInterval index_range;
                    if(!integerInterval(t,{index,close},integer_bounds,index_range)) return quantified;
                    Bounds carrier{};
                    const auto cells=bounded_cells.find(std::string(symbolIdentity(t[array])));
                    if(cells==bounded_cells.end() ||
                       !indexIntervalCovered(cells->second,index_range.lo,index_range.hi,carrier)) return quantified;
                    bounds.emplace(key,carrier);
                }
                allowed_array_symbol_tokens.insert(array);
            }
        }
    }
    for(std::size_t i=0;i<t.size();++i) {
        if(t[i].list || t[i].string_literal) continue;
        if(bounded_set_arrays.count(std::string(symbolIdentity(t[i]))) && !allowed_array_symbol_tokens.count(i))
            return quantified;
    }
    return false;
}
bool hasScopedAssertionContext(const std::vector<Token>& t) {
    bool saw_check=false;
    for(std::size_t p=0;p<t.size();) {
        const auto q=next(t,p); if(q<=p) return true;
        if(!t[p].list || t[p].text!="(" || p+1>=q) { p=q; continue; }
        const auto head=t[p+1].text;
        if(head=="push" || head=="pop" || head=="reset" || head=="reset-assertions") return true;
        if(head=="check-sat" || head=="check-sat-assuming") saw_check=true;
        // A later assertion belongs to a subsequent check-sat state. A proof
        // collected across that boundary could rewrite an earlier query using
        // a constraint which was not active at that query.
        if(saw_check && head=="assert") return true;
        p=q;
    }
    return false;
}

struct Rewriter {
    const std::vector<Token>& t; const BoundMap& bounds; const std::unordered_set<std::string>& names;
    const bool bound_context_unsupported;
    const bool finite_array_operations;
    const std::unordered_set<std::string>& safe_let_names;
    std::string subset_name;
    std::unordered_map<std::string,std::size_t> scoped_names;
    struct LocalSupport { std::size_t depth; std::vector<std::string> elements; };
    std::unordered_map<std::string,std::vector<LocalSupport>> local_supports;
    std::size_t support_serial=0;
    std::size_t cardinality_set_serial=0;
    Rewriter(const std::vector<Token>& tt,const BoundMap& bb,const std::unordered_set<std::string>& nn,bool context_unsupported,const std::unordered_set<std::string>& safe_lets,bool finite_ops=false):t(tt),bounds(bb),names(nn),bound_context_unsupported(context_unsupported),finite_array_operations(finite_ops),safe_let_names(safe_lets) {
        std::size_t n=0; do { subset_name="__somt_z3_set_subset_element"+(n?"_"+std::to_string(n):""); ++n; } while(names.count(subset_name));
    }
    void sortExpr(Range r,std::string& out) {
        struct Pending { Range range; bool space=false; bool close=false; };
        std::vector<Pending> pending{{r,false,false}};
        while(!pending.empty()) {
            const auto current=pending.back(); pending.pop_back();
            if(current.close) { out+=')'; continue; }
            if(current.space) out+=' ';
            const auto term=current.range;
            if(listHead(t,term.first,"Set") && t[term.first].mate+1==term.second) {
                const auto elem=term.first+2;
                if(!is(t,elem,"Int") || next(t,elem)!=t[term.first].mate)
                    throw std::runtime_error("Z3 set lowering supports only Set Int");
                out+="(Array Int Bool)";
            } else if(term.first<term.second && t[term.first].list && t[term.first].text=="(" && t[term.first].mate+1==term.second) {
                out+='('; pending.push_back({{},false,true});
                std::vector<Range> children;
                for(auto p=term.first+1;p<t[term.first].mate;p=next(t,p)) children.emplace_back(p,next(t,p));
                for(std::size_t i=children.size();i>0;--i) pending.push_back({children[i-1],i>1,false});
            } else appendRange(t,term,out);
        }
    }
    void constructorList(Range r,std::string& out) {
        if(!is(t,r.first,"(") || t[r.first].mate+1!=r.second) throw std::runtime_error("Z3 datatype constructor list malformed");
        out+="(";
        for(std::size_t c=r.first+1;c<t[r.first].mate;) {
            const auto ce=next(t,c); if(!is(t,c,"(")) throw std::runtime_error("Z3 datatype constructor malformed");
            if(c>r.first+1) { out+=' '; } out+='('; appendRange(t,{c+1,next(t,c+1)},out);
            for(std::size_t f=next(t,c+1);f<t[c].mate;) {
                const auto fe=next(t,f); if(!is(t,f,"(")) throw std::runtime_error("Z3 datatype selector malformed");
                std::size_t name=f+1, sort=next(t,name); if(next(t,sort)!=t[f].mate) throw std::runtime_error("Z3 datatype selector sort malformed");
                out+=" ("; appendRange(t,{name,next(t,name)},out); out+=' '; sortExpr({sort,t[f].mate},out); out+=')'; f=fe;
            }
            out+=')'; c=ce;
        }
        out+=')';
    }
    void datatypeDefinition(Range r,std::string& out) {
        if(listHead(t,r.first,"par") && t[r.first].mate+1==r.second) {
            std::size_t params=r.first+2, ctors=next(t,params); if(!is(t,params,"(") || next(t,ctors)!=t[r.first].mate) throw std::runtime_error("Z3 parameterized datatype malformed");
            out+="(par ("; appendRange(t,{params+1,t[params].mate},out); out+=") "; constructorList({ctors,t[r.first].mate},out); out+=')';
        } else constructorList(r,out);
    }
    bool operandUsesShadowedName(Range r) const {
        for(std::size_t i=r.first;i<r.second;++i) {
            if(t[i].list || t[i].string_literal) continue;
            const auto name=std::string(symbolIdentity(t[i]));
            if(scoped_names.count(name) && !safe_let_names.count(name)) return true;
        }
        return false;
    }
    void pushNames(const std::vector<std::string>& added) {
        for(const auto& name:added) ++scoped_names[name];
    }
    void popNames(const std::vector<std::string>& added) {
        for(const auto& name:added) { auto it=scoped_names.find(name); if(it!=scoped_names.end() && --it->second==0) scoped_names.erase(it); }
    }
    static std::string intTerm(std::int64_t value) {
        if(value>=0) return std::to_string(value);
        const std::uint64_t magnitude=std::uint64_t{0}-static_cast<std::uint64_t>(value);
        return "(- "+std::to_string(static_cast<unsigned long long>(magnitude))+")";
    }
    static bool intLiteral(std::string_view text,std::int64_t& value) {
        if(text.empty()) return false;
        if(text.front()!='(') {
            try { std::string s(text); std::size_t used=0; long long n=std::stoll(s,&used); if(used==s.size() && n>=0) { value=n; return true; } } catch(...){}
            return false;
        }
        constexpr std::string_view prefix="(- ";
        if(text.substr(0,prefix.size())!=prefix || text.back()!=')') return false;
        const auto magnitude=text.substr(prefix.size(),text.size()-prefix.size()-1);
        if(magnitude=="9223372036854775808") { value=std::numeric_limits<std::int64_t>::min(); return true; }
        try { std::string s(magnitude); std::size_t used=0; long long n=std::stoll(s,&used); if(used==s.size() && n>0) { value=-n; return true; } } catch(...){}
        return false;
    }
    static bool isEmptySet(const std::vector<Token>& t,Range r) {
        return listHead(t,r.first,"as") && r.second==t[r.first].mate+1 && is(t,r.first+2,"set.empty");
    }
    void appendCandidate(std::vector<std::string>& values,std::string value) const {
        // Keep duplicates here. cardinalityTerm emits an equality guard for
        // non-distinct symbolic candidates, so exactness does not depend on
        // quadratic host-side deduplication.
        values.push_back(std::move(value));
    }
    bool finiteSupportImpl(Range r,std::vector<std::string>& values) {
        if(r.second==r.first+1 && !t[r.first].list && !t[r.first].string_literal) {
            const std::string name(symbolIdentity(t[r.first]));
            const auto support=local_supports.find(name);
            const auto depth=scoped_names.find(name);
            if(support!=local_supports.end() && !support->second.empty()
               && depth!=scoped_names.end() && support->second.back().depth==depth->second) {
                const auto& elements=support->second.back().elements;
                values.insert(values.end(),elements.begin(),elements.end());
                return true;
            }
        }
        const std::string key=proofKey(t,r);
        if(!operandUsesShadowedName(r)) {
            const auto proof=bounds.find(key);
            if(proof!=bounds.end()) {
                if(proof->second.lo<=proof->second.hi) {
                    const std::uint64_t distance=static_cast<std::uint64_t>(proof->second.hi)
                        -static_cast<std::uint64_t>(proof->second.lo);
                    if(distance>=values.max_size()-values.size())
                        throw std::length_error("Z3 set.card exact interval support exceeds the host vector representation");
                    const auto count=static_cast<std::size_t>(distance)+1;
                    values.reserve(values.size()+count);
                    for(std::int64_t n=proof->second.lo;;++n) { values.push_back(intTerm(n)); if(n==proof->second.hi) break; }
                }
                return true;
            }
        }
        if(isEmptySet(t,r)) return true;
        if(!listHead(t,r.first,"set.singleton") || t[r.first].mate+1!=r.second) {
            // Try the other finite set constructors below.
        } else {
            const std::size_t e=r.first+2; if(next(t,e)!=t[r.first].mate) throw std::runtime_error("Z3 set.singleton malformed arity");
            std::string element; expr({e,t[r.first].mate},element);
            appendCandidate(values,std::move(element)); return true;
        }
        if(listHead(t,r.first,"set.insert") && t[r.first].mate+1==r.second) {
            std::vector<Range> args; for(std::size_t p=r.first+2;p<t[r.first].mate;) { auto q=next(t,p); args.emplace_back(p,q); p=q; }
            if(args.size()<2) throw std::runtime_error("Z3 set.insert malformed arity");
            std::vector<std::string> base;
            if(!finiteSupport(args.back(),base)) return false;
            values.insert(values.end(),base.begin(),base.end());
            for(std::size_t i=0;i+1<args.size();++i) {
                std::string element; expr(args[i],element);
                appendCandidate(values,std::move(element));
            }
            return true;
        }
        if(listHead(t,r.first,"set.union") && t[r.first].mate+1==r.second) {
            std::vector<Range> args; for(std::size_t p=r.first+2;p<t[r.first].mate;) { auto q=next(t,p); args.emplace_back(p,q); p=q; }
            if(args.size()<2) throw std::runtime_error("Z3 set.union malformed arity");
            std::vector<std::string> all;
            for(const auto& arg:args) { std::vector<std::string> part; if(!finiteSupport(arg,part)) return false; for(auto& v:part) appendCandidate(all,std::move(v)); }
            values.insert(values.end(),all.begin(),all.end()); return true;
        }
        if(listHead(t,r.first,"set.inter") && t[r.first].mate+1==r.second) {
            for(std::size_t p=r.first+2;p<t[r.first].mate;) { auto q=next(t,p); std::vector<std::string> part; if(finiteSupport({p,q},part)) { values.insert(values.end(),part.begin(),part.end()); return true; } p=q; }
            return false;
        }
        if(listHead(t,r.first,"set.minus") && t[r.first].mate+1==r.second) {
            std::size_t left=r.first+2, right=next(t,left); (void)right; return finiteSupport({left,right},values);
        }
        return false;
    }
    std::string cardinalityTerm(Range set) {
        std::vector<std::string> support;
        if(!finiteSupport(set,support)) {
            const auto key=proofKey(t,set);
            if(bounds.count(key) && operandUsesShadowedName(set))
                throw std::runtime_error("Z3 set.card unsupported: finite-carrier proof for `"+canonical(t,set)+"` is shadowed by a lexical binding at this use");
            if(bound_context_unsupported)
                throw std::runtime_error("Z3 set.card unsupported: asserted interval proofs are disabled across push/pop/reset or later-check assertion contexts");
            throw std::runtime_error("Z3 set.card unsupported: no exact finite support or unconditional asserted interval proof for operand `"+canonical(t,set)+"`");
        }
        if(support.empty()) return "0";

        // Partition support into unique literals and unique symbolic terms.
        // Integer literals are normalized by value (including SMT's `(- n)`
        // form); other terms are deduplicated only by exact emitted syntax.
        // Distinct symbolic terms still need equality guards because they may
        // evaluate equally.
        std::vector<std::string> literal_support, symbolic_support;
        literal_support.reserve(support.size());
        symbolic_support.reserve(support.size());
        std::unordered_set<std::int64_t> seen_integer_literals;
        std::unordered_set<std::string> seen_symbolic_terms;
        for(auto& term:support) {
            std::int64_t integer=0;
            if(intLiteral(term,integer)) {
                if(seen_integer_literals.insert(integer).second)
                    literal_support.push_back(std::move(term));
            } else if(seen_symbolic_terms.insert(term).second) {
                symbolic_support.push_back(std::move(term));
            }
        }
        if(literal_support.empty() && symbolic_support.empty()) return "0";
        const std::size_t unique_count=literal_support.size()+symbolic_support.size();

        std::string rendered_set;
        expr(set,rendered_set);
        std::string set_name;
        const bool bind_set=unique_count>1;
        if(bind_set) {
            do { set_name="__somt_z3_set_card_set_"+std::to_string(cardinality_set_serial++); }
            while(names.count(set_name) || scoped_names.count(set_name));
        }
        const std::string& set_term=bind_set ? set_name : rendered_set;
        std::string formula;
        const auto append=[&](std::string_view piece) {
            if(piece.size()>formula.max_size()-formula.size()) throw std::length_error("Z3 set.card exact expression exceeds the host string representation");
            formula.append(piece.data(),piece.size());
        };
        if(unique_count>1) append("(+");

        // Literals are the first representative of their values. They never
        // need comparisons with another literal. Each symbolic term then
        // checks against all literals and prior symbolic terms, so an equal
        // symbolic value is counted exactly once. Host work is O(c*s+s^2),
        // rather than scanning all c previous literals for every literal.
        for(const auto& literal:literal_support) {
            append(" (ite (select "); append(set_term); append(" ");
            append(literal); append(") 1 0)");
        }
        for(std::size_t i=0;i<symbolic_support.size();++i) {
            append(" (ite (and (select "); append(set_term); append(" ");
            append(symbolic_support[i]); append(")");
            for(const auto& literal:literal_support) {
                append(" (not (= "); append(symbolic_support[i]); append(" ");
                append(literal); append("))");
            }
            for(std::size_t j=0;j<i;++j) {
                append(" (not (= "); append(symbolic_support[i]); append(" ");
                append(symbolic_support[j]); append("))");
            }
            append(" ) 1 0)");
        }
        if(unique_count>1) append(")");
        if(bind_set) return "(let (("+set_name+" "+rendered_set+")) "+formula+")";
        return formula.substr(1); // remove the one leading space before ite
    }
    struct RewriteRequest { Range range; bool support=false; bool top_level=false; };
    struct RewriteResult {
        RewriteRequest request;
        std::string text;
        std::vector<std::string> support;
        bool finite=false;
        std::size_t support_serial=0, cardinality_serial=0;
    };
    struct RewriteState {
        std::unordered_map<std::string,std::size_t> scoped;
        std::unordered_map<std::string,std::vector<LocalSupport>> supports;
        std::size_t support_serial=0, cardinality_serial=0;
    };
    struct RewriteFrame {
        RewriteRequest request;
        RewriteState initial;
        std::vector<RewriteResult> children;
        std::size_t cursor=0;
    };
    struct NeedRewrite { RewriteRequest request; };
    RewriteFrame* active_frame=nullptr;
    RewriteState state() const { return {scoped_names,local_supports,support_serial,cardinality_set_serial}; }
    void restore(const RewriteState& initial) {
        scoped_names=initial.scoped; local_supports=initial.supports;
        support_serial=initial.support_serial; cardinality_set_serial=initial.cardinality_serial;
    }
    const RewriteResult& dependency(RewriteRequest request) {
        if(active_frame->cursor==active_frame->children.size()) throw NeedRewrite{request};
        const auto& result=active_frame->children[active_frame->cursor++];
        if(result.request.range!=request.range || result.request.support!=request.support || result.request.top_level!=request.top_level)
            throw std::logic_error("finite-set lowering: inconsistent work queue replay");
        support_serial=result.support_serial; cardinality_set_serial=result.cardinality_serial;
        return result;
    }
    RewriteResult runRewrite(RewriteRequest request) {
        const auto original=state();
        std::vector<RewriteFrame> pending;
        pending.push_back({request,original,{},0});
        try {
            while(!pending.empty()) {
                active_frame=&pending.back();
                active_frame->cursor=0; restore(active_frame->initial);
                RewriteResult result; result.request=active_frame->request;
                try {
                    if(result.request.support) result.finite=finiteSupportImpl(result.request.range,result.support);
                    else exprImpl(result.request.range,result.text,result.request.top_level);
                    result.support_serial=support_serial; result.cardinality_serial=cardinality_set_serial;
                } catch(const NeedRewrite& need) {
                    auto child_state=state();
                    pending.push_back({need.request,std::move(child_state),{},0});
                    continue;
                }
                pending.pop_back();
                if(pending.empty()) { active_frame=nullptr; return result; }
                pending.back().children.push_back(std::move(result));
            }
        } catch(...) { active_frame=nullptr; restore(original); throw; }
        throw std::logic_error("finite-set lowering: empty work queue");
    }
    void expr(Range r,std::string& out,bool top_level=false) {
        if(active_frame) { out+=dependency({r,false,top_level}).text; return; }
        out+=runRewrite({r,false,top_level}).text;
    }
    bool finiteSupport(Range r,std::vector<std::string>& values) {
        if(active_frame) {
            const auto& result=dependency({r,true,false});
            values.insert(values.end(),result.support.begin(),result.support.end()); return result.finite;
        }
        const auto result=runRewrite({r,true,false});
        values.insert(values.end(),result.support.begin(),result.support.end()); return result.finite;
    }
    std::string freshOperand() {
        std::string fresh;
        do { fresh="__somt_oms_set_operand_"+std::to_string(support_serial++); }
        while(names.count(fresh) || scoped_names.count(fresh));
        return fresh;
    }
    std::string finiteOperation(Range whole,const std::vector<Range>& args,std::string_view operation) {
        std::vector<std::string> support;
        // For intersection one finite operand suffices, for difference the
        // left operand suffices, and union requires every operand finite.
        if(!finiteSupport(whole,support))
            throw std::runtime_error("OptiMathSAT set operation requires a proved finite carrier: "+canonical(t,whole));
        std::vector<std::string> operands;
        std::string bindings="(let (";
        for(const auto& arg:args) {
            const auto name=freshOperand(); std::string value; expr(arg,value);
            bindings+="("+name+" "+value+")"; operands.push_back(name);
        }
        bindings+=") ";
        std::string result; result.reserve(bindings.size()+support.size()*32);
        result+=bindings;
        for(std::size_t i=0;i<support.size();++i) result+="(store ";
        result+="((as const (Array Int Bool)) false)";
        // Equal symbolic candidates write equal membership formulas, so this
        // exact extensional construction needs no distinctness assumption.
        for(auto it=support.rbegin();it!=support.rend();++it) {
            result+=" "+*it+" (";
            result+=(operation=="union"?"or":"and");
            for(std::size_t i=0;i<operands.size();++i) {
                result+=' ';
                if(operation=="minus" && i==1) result+="(not ";
                result+="(select "+operands[i]+" "+*it+")";
                if(operation=="minus" && i==1) result+=')';
            }
            result+="))";
        }
        result+=')'; return result;
    }
    void exprImpl(Range r,std::string& out,bool top_level) {
        if(r.first>=r.second) return;
        if(!t[r.first].list || t[r.first].text!="(") { out.append(t[r.first].text.data(),t[r.first].text.size()); return; }
        const std::size_t close=t[r.first].mate, h=r.first+1;
        if(close+1!=r.second) throw std::runtime_error("Z3 set lowering: malformed term span");
        if(top_level && keyword(t,h,"set-logic")) {
            // The representation adds arrays and subset quantifiers even when
            // the source selected a quantifier-free arithmetic logic.
            out+="(set-logic ALL)"; return;
        }
        if(keyword(t,h,"match") && containsHead(t,r,"set.card"))
            throw std::runtime_error("Z3 set.card unsupported under match pattern binders");
        if(keyword(t,h,"forall") || keyword(t,h,"exists") || keyword(t,h,"lambda")) {
            std::size_t binders=h+1, body=next(t,binders); if(!is(t,binders,"(") || next(t,body)!=close) throw std::runtime_error("Z3 quantifier/lambda malformed arity");
            std::vector<std::string> added;
            out+='('; appendRange(t,{h,h+1},out); out+=" (";
            for(std::size_t p=binders+1;p<t[binders].mate;) {
                const auto q=next(t,p); if(!is(t,p,"(")) throw std::runtime_error("Z3 quantifier/lambda malformed binder");
                std::size_t name=p+1, sort=next(t,name); if(next(t,sort)!=t[p].mate) throw std::runtime_error("Z3 quantifier/lambda malformed binder sort");
                if(p>binders+1) { out+=' '; } out+='('; appendRange(t,{name,next(t,name)},out); out+=' '; sortExpr({sort,t[p].mate},out); out+=')';
                added.emplace_back(symbolIdentity(t[name])); p=q;
            }
            out+=") "; pushNames(added); expr({body,close},out); popNames(added); out+=')'; return;
        }
        if(keyword(t,h,"let")) {
            std::size_t bindings=h+1, body=next(t,bindings); if(!is(t,bindings,"(") || next(t,body)!=close) throw std::runtime_error("Z3 let malformed arity");
            std::vector<std::string> added;
            std::vector<std::pair<std::string,std::vector<std::string>>> supports;
            const bool needs_support=finite_array_operations || containsHead(t,{body,close},"set.card");
            out+="(let (";
            for(std::size_t p=bindings+1;p<t[bindings].mate;) {
                const auto q=next(t,p); if(!is(t,p,"(")) throw std::runtime_error("Z3 let malformed binding");
                std::size_t name=p+1, value=next(t,name); if(next(t,value)!=t[p].mate) throw std::runtime_error("Z3 let malformed binding value");
                if(p>bindings+1) { out+=' '; } out+='('; appendRange(t,{name,next(t,name)},out); out+=' '; expr({value,t[p].mate},out); out+=')';
                const std::string identity(symbolIdentity(t[name]));
                std::vector<std::string> elements;
                if(needs_support && finiteSupport({value,t[p].mate},elements)) {
                    // SMT let bindings are simultaneous. Capture each support
                    // element in a fresh sibling binding, before body binders
                    // can shadow names occurring in the original element.
                    for(auto& element:elements) {
                        std::string fresh;
                        do { fresh="__somt_z3_set_support_"+std::to_string(support_serial++); }
                        while(names.count(fresh));
                        out+=" ("+fresh+" "+element+")";
                        element=std::move(fresh);
                    }
                    supports.emplace_back(identity,std::move(elements));
                }
                added.push_back(identity); p=q;
            }
            out+=") "; pushNames(added);
            for(auto& support:supports)
                local_supports[support.first].push_back({scoped_names.at(support.first),std::move(support.second)});
            expr({body,close},out);
            for(const auto& support:supports) {
                auto found=local_supports.find(support.first);
                found->second.pop_back();
                if(found->second.empty()) local_supports.erase(found);
            }
            popNames(added); out+=')'; return;
        }
        if(top_level && keyword(t,h,"declare-const")) {
            std::size_t name=h+1, sort=next(t,name); if(next(t,sort)!=close) throw std::runtime_error("Z3 declare-const malformed arity");
            out+="(declare-const "; appendRange(t,{name,next(t,name)},out); out+=' '; sortExpr({sort,close},out); out+=')'; return;
        }
        if(top_level && keyword(t,h,"declare-fun")) {
            std::size_t name=h+1, args=next(t,name), result=next(t,args); if(next(t,result)!=close || !is(t,args,"(")) throw std::runtime_error("Z3 declare-fun malformed arity");
            out+="(declare-fun "; appendRange(t,{name,next(t,name)},out); out+=" (";
            for(std::size_t p=args+1;p<t[args].mate;) { if(p>args+1) { out+=' '; } auto q=next(t,p); sortExpr({p,q},out); p=q; }
            out+=") "; sortExpr({result,close},out); out+=')'; return;
        }
        if(top_level && (keyword(t,h,"define-fun") || keyword(t,h,"define-fun-rec"))) {
            std::size_t name=h+1, binders=next(t,name), result=next(t,binders), body=next(t,result); if(next(t,body)!=close || !is(t,binders,"(")) throw std::runtime_error("Z3 define-fun malformed arity");
            out+='('; appendRange(t,{h,h+1},out); out+=' '; appendRange(t,{name,next(t,name)},out); out+=" (";
            std::vector<std::string> added;
            for(std::size_t p=binders+1;p<t[binders].mate;) { auto q=next(t,p);
                if(!is(t,p,"(")) throw std::runtime_error("Z3 define-fun malformed formal");
                std::size_t formal_name=p+1, formal_sort=next(t,formal_name); if(next(t,formal_sort)!=t[p].mate) throw std::runtime_error("Z3 define-fun malformed formal sort");
                if(p>binders+1) { out+=' '; } out+='('; appendRange(t,{formal_name,next(t,formal_name)},out); out+=' '; sortExpr({formal_sort,t[p].mate},out); out+=')'; added.emplace_back(symbolIdentity(t[formal_name])); p=q;
            }
            out+=") "; sortExpr({result,next(t,result)},out); out+=' '; pushNames(added); expr({body,close},out); popNames(added); out+=')'; return;
        }
        if(top_level && keyword(t,h,"define-funs-rec")) {
            std::size_t signatures=h+1, bodies=next(t,signatures);
            if(!is(t,signatures,"(") || !is(t,bodies,"(") || next(t,bodies)!=close)
                throw std::runtime_error("Z3 define-funs-rec malformed arity");
            out+="(define-funs-rec (";
            std::vector<std::vector<std::string>> function_formals;
            for(std::size_t p=signatures+1;p<t[signatures].mate;) {
                const auto sig_end=next(t,p); if(!is(t,p,"(")) throw std::runtime_error("Z3 define-funs-rec malformed signature");
                std::size_t name=p+1, formals=next(t,name), result=next(t,formals);
                if(!is(t,formals,"(") || next(t,result)!=t[p].mate) throw std::runtime_error("Z3 define-funs-rec malformed signature fields");
                std::vector<std::string> added;
                if(p>signatures+1) { out+=' '; } out+='('; appendRange(t,{name,next(t,name)},out); out+=" (";
                for(std::size_t f=formals+1;f<t[formals].mate;) {
                    const auto formal_end=next(t,f); if(!is(t,f,"(")) throw std::runtime_error("Z3 define-funs-rec malformed formal");
                    std::size_t formal_name=f+1, formal_sort=next(t,formal_name);
                    if(next(t,formal_sort)!=t[f].mate) throw std::runtime_error("Z3 define-funs-rec malformed formal sort");
                    if(f>formals+1) { out+=' '; } out+='('; appendRange(t,{formal_name,next(t,formal_name)},out); out+=' '; sortExpr({formal_sort,t[f].mate},out); out+=')'; added.emplace_back(symbolIdentity(t[formal_name])); f=formal_end;
                }
                out+=") "; sortExpr({result,t[p].mate},out); out+=')'; function_formals.push_back(std::move(added)); p=sig_end;
            }
            out+=") (";
            std::size_t index=0;
            for(std::size_t p=bodies+1;p<t[bodies].mate;) { const auto q=next(t,p); if(p>bodies+1) { out+=' '; } if(index>=function_formals.size()) throw std::runtime_error("Z3 define-funs-rec body count mismatch"); pushNames(function_formals[index]); expr({p,q},out); popNames(function_formals[index]); p=q; ++index; }
            if(index!=function_formals.size()) throw std::runtime_error("Z3 define-funs-rec body count mismatch");
            out+="))"; return;
        }
        if(top_level && keyword(t,h,"define-sort")) {
            std::size_t name=h+1, params=next(t,name), body=next(t,params);
            if(next(t,body)!=close || !is(t,params,"(")) throw std::runtime_error("Z3 define-sort malformed arity");
            out+="(define-sort "; appendRange(t,{name,next(t,name)},out); out+=" (";
            appendRange(t,{params+1,t[params].mate},out); out+=") "; sortExpr({body,close},out); out+=')'; return;
        }
        if(top_level && keyword(t,h,"declare-datatype")) {
            std::size_t name=h+1, ctors=next(t,name); if(next(t,ctors)!=close) throw std::runtime_error("Z3 declare-datatype malformed arity");
            out+="(declare-datatype "; appendRange(t,{name,next(t,name)},out); out+=' '; constructorList({ctors,close},out); out+=')'; return;
        }
        if(top_level && (keyword(t,h,"declare-datatypes") || keyword(t,h,"declare-codatatypes"))) {
            std::size_t names=h+1, defs=next(t,names); if(!is(t,names,"(") || !is(t,defs,"(") || next(t,defs)!=close) throw std::runtime_error("Z3 declare-datatypes malformed arity");
            out+='('; appendRange(t,{h,h+1},out); out+=" ("; appendRange(t,{names+1,t[names].mate},out); out+=") (";
            for(std::size_t p=defs+1;p<t[defs].mate;) { const auto q=next(t,p); if(p>defs+1) { out+=' '; } datatypeDefinition({p,q},out); p=q; }
            out+="))"; return;
        }
        if(keyword(t,h,"as") && h+3<close && (is(t,h+1,"set.empty")||is(t,h+1,"set.universe"))) {
            if(is(t,h+1,"set.universe")) throw std::runtime_error("Z3 set.universe unsupported: array encoding cannot preserve the input-dependent finite universe");
            std::size_t sr=h+2; if(!listHead(t,sr,"Set")) throw std::runtime_error("Z3 set.empty has malformed sort");
            out+="((as const "; sortExpr({sr,next(t,sr)},out); out+=") false)"; return;
        }
        if(keyword(t,h,"as")) {
            std::size_t symbol=h+1, sort=next(t,symbol); if(next(t,sort)!=close) throw std::runtime_error("Z3 ascription malformed arity");
            out+="(as "; appendRange(t,{symbol,next(t,symbol)},out); out+=' '; sortExpr({sort,close},out); out+=')'; return;
        }
        if(is(t,h,"set.universe")) throw std::runtime_error("Z3 set.universe unsupported: array encoding cannot preserve the input-dependent finite universe");
        if(is(t,h,"set.complement")) throw std::runtime_error("Z3 set.complement unsupported: it is relative to the input-dependent finite set universe");
        if(is(t,h,"set.card")) {
            std::size_t a=h+1,ae=next(t,a); if(ae!=close) throw std::runtime_error("Z3 set.card malformed arity");
            out+=cardinalityTerm({a,ae}); return;
        }
        if(is(t,h,"set.member")) {
            std::size_t a=h+1,ae=next(t,a),b=ae,be=next(t,b); if(be!=close) throw std::runtime_error("Z3 set.member malformed arity");
            out+="(select "; expr({b,be},out); out+=' '; expr({a,ae},out); out+=')'; return;
        }
        if(is(t,h,"set.union")||is(t,h,"set.inter")) {
            const char* op=is(t,h,"set.union")?"or":"and"; std::vector<Range> args; for(std::size_t p=h+1;p<close;) { auto q=next(t,p); args.emplace_back(p,q); p=q; }
            if(args.size()<2) throw std::runtime_error("Z3 set union/intersection needs at least two operands");
            if(finite_array_operations) { out+=finiteOperation(r,args,is(t,h,"set.union")?"union":"inter"); return; }
            std::string left; expr(args[0],left);
            for(std::size_t j=1;j<args.size();++j) { std::string right; expr(args[j],right); left=std::string("((_ map ")+op+") "+left+" "+right+")"; }
            out+=left; return;
        }
        if(is(t,h,"set.minus")) {
            std::size_t a=h+1,ae=next(t,a),b=ae,be=next(t,b); if(be!=close) throw std::runtime_error("Z3 set.minus malformed arity");
            if(finite_array_operations) { out+=finiteOperation(r,{{a,ae},{b,be}},"minus"); return; }
            // Built-in maps need no auxiliary declaration, so they also work
            // in scripts without set-logic and across reset commands.
            out+="((_ map and) "; expr({a,ae},out); out+=" ((_ map not) "; expr({b,be},out); out+="))"; return;
        }
        if(is(t,h,"set.insert")) {
            std::vector<Range> args; for(std::size_t p=h+1;p<close;) { auto q=next(t,p); args.emplace_back(p,q); p=q; }
            if(args.size()<2) throw std::runtime_error("Z3 set.insert malformed arity");
            // Build nested stores from the set operand outwards.
            std::string value; expr(args.back(),value);
            for(std::size_t j=args.size()-1;j>0;--j) { std::string element; expr(args[j-1],element); value="(store "+value+" "+element+" true)"; }
            out+=value; return;
        }
        if(is(t,h,"set.singleton")) {
            std::size_t value=h+1; if(next(t,value)!=close) throw std::runtime_error("Z3 set.singleton malformed arity");
            out+="(store ((as const (Array Int Bool)) false) "; expr({value,close},out); out+=" true)"; return;
        }
        if(is(t,h,"set.subset")) {
            std::size_t a=h+1,ae=next(t,a),b=ae,be=next(t,b); if(be!=close) throw std::runtime_error("Z3 set.subset malformed arity");
            if(finite_array_operations) {
                std::vector<std::string> support;
                if(!finiteSupport({a,ae},support)) throw std::runtime_error("OptiMathSAT set.subset requires a proved finite left carrier");
                const auto left=freshOperand(),right=freshOperand();
                out+="(let (("+left+" "; expr({a,ae},out); out+=") ("+right+" "; expr({b,be},out); out+=")) (and";
                for(const auto& element:support) out+=" (=> (select "+left+" "+element+") (select "+right+" "+element+"))";
                out+="))"; return;
            }
            out+="(forall (("+subset_name+" Int)) (=> (select "; expr({a,ae},out); out+=" "+subset_name+") (select "; expr({b,be},out); out+=" "+subset_name+")))"; return;
        }
        out+='('; for(std::size_t p=r.first+1;p<close;) { if(p>r.first+1) { out+=' '; } auto q=next(t,p); expr({p,q},out); p=q; } out+=')';
    }
};

void gatherNames(const std::vector<Token>& t,std::unordered_set<std::string>& names) { for(const auto& x:t) if(!x.list && !x.string_literal) names.emplace(symbolIdentity(x)); }
}

std::string lowerFiniteSets(const std::string& smt2,bool finite_array_operations) {
    const auto tokens=tokenize(smt2);
    BoundMap bounds; findBounds(tokens,{0,tokens.size()},bounds);
    const bool scoped_context=hasScopedAssertionContext(tokens);
    if(scoped_context) bounds.clear();
    std::unordered_set<std::string> safe_let_symbols;
    if(hasQuantifiedSet(tokens,bounds,scoped_context,safe_let_symbols))
        throw std::runtime_error("Z3 set lowering refuses quantified Set formulas with unbounded carriers: HIR Set is finite, but Array Int Bool admits infinite subsets");
    std::unordered_set<std::string> names; gatherNames(tokens,names); Rewriter rw(tokens,bounds,names,scoped_context,safe_let_symbols,finite_array_operations);
    std::string output;
    const std::size_t reserve_extra=smt2.size()/8;
    if(reserve_extra>output.max_size()-smt2.size())
        throw std::length_error("Z3 set lowering output exceeds the host string representation");
    output.reserve(smt2.size()+reserve_extra);
    for(std::size_t p=0;p<tokens.size();) { std::size_t q=next(tokens,p); if(q<=p) throw std::runtime_error("Z3 set lowering: invalid token tree"); std::string command; rw.expr({p,q},command,true); output+=command; output+='\n'; p=q; }
    return output;
}
std::string lowerFiniteSetsForZ3(const std::string& smt2) {
    return lowerFiniteSets(smt2,false);
}
std::string lowerFiniteSetsForOptiMathSat(const std::string& smt2) {
    return lowerFiniteSets(smt2,true);
}
}
