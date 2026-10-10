"""Search stack schedules for the recognizer's normal iteration.
Top-of-stack is index zero. Computations are a fixed exact-expression DAG.
"""
import heapq

inputs = ('a', 'o', 'w', 'f', 'm', 'c', 's')
target = ('a', 'o', 'W', 'f', 'm', 'c', 's')
# Computation result, inputs, commutative flag, opcode
nodes = [('z', ('c','c'), True, 'ADD'),
         ('h', ('z','m'), True, 'AND'),
         ('u', ('w','h'), True, 'OR'),
         ('v', ('h','c'), True, 'OR'),
         ('j', ('k','v'), False, 'SHR'),
         ('q', ('u','j'), False, 'SUB'),
         ('x', ('q','u'), True, 'XOR'),
         ('W', ('x','w'), True, 'XOR')]

def solve(width=150000, depth=20):
    beam = [(inputs, 0, ())]
    seen = {}
    for d in range(depth+1):
        next_states = {}
        for st, done, path in beam:
            if st == target:
                print('FOUND', len(path), path, flush=True); return path
            options = []
            for i, (res, args, comm, op) in enumerate(nodes):
                if done & (1 << i): continue
                if st[:len(args)] == args or (comm and st[:len(args)] == args[::-1]):
                    options.append(((res,) + st[len(args):], done | 1 << i, op))
            if 'k' not in st and not done & 16:
                options.append((('k',) + st, done, 'PUSH1 4'))
            needed = set(target)
            for i, (_, args, _, _) in enumerate(nodes):
                if not done & (1 << i): needed.update(args)
            if len(st) < 12:
                for i, v in enumerate(st[:16]):
                    if v in needed and st.count(v) < 3:
                        options.append(((v,) + st, done, f'DUP{i+1}'))
            for i in range(1, min(len(st), 17)):
                if st[i] != st[0]:
                    ns = list(st); ns[0], ns[i] = ns[i], ns[0]
                    options.append((tuple(ns), done, f'SWAP{i}'))
            if st and (st[0] not in needed or st.count(st[0]) > 1):
                options.append((st[1:], done, 'POP'))
            for ns, nd, op in options:
                key=(ns, nd)
                if seen.get(key, 100) <= d+1: continue
                # A consumed leaf cannot be produced again.
                available=set(ns)
                for j,(res,args,_,_) in enumerate(nodes):
                    if not nd & (1<<j): available.add(res)
                remaining = set(target)
                for j, (_, args, _, _) in enumerate(nodes):
                    if not nd & (1 << j): remaining.update(args)
                if not remaining.issubset(available | {'k'}): continue
                seen[key]=d+1
                missing = sum(x not in ns for x in target)
                mismatches = sum(i >= len(ns) or ns[i] != x for i,x in enumerate(target))
                score = 4 * nd.bit_count() - missing - .3 * mismatches - .2 * len(ns)
                next_states[key]=(score, ns, nd, path+(op,))
        best=heapq.nlargest(width, next_states.values())
        beam=[(st, done, path) for _,st,done,path in best]
        print('depth',d,'states',len(next_states), 'best',best[0][0] if best else None,flush=True)
    return None

if __name__ == '__main__': solve()
