import sys, os, re
sys.path.insert(0, r'C:\Users\xingg\Desktop\命运计划\Fate-world-prediction\_migration')
import refgraph
m = refgraph.scan()
cap = 'Integration.ModelingBatch1'
print('cap imports:', sorted(m[cap]['imports']))
print()
for mod, names in [('Modeling.CFMap', ['not_injective_iff_nontrivial_fiber']),
                   ('Modeling.FiniteCondIndep', ['sum_margXZ', 'sum_margYZ']),
                   ('Modeling.CondIndepGeneralNZ', ['notMemXZ_memY', 'notMemYZ_memX'])]:
    for n in names:
        in_decls = n in m[mod]['decls']
        in_body = re.search(r'(?<![\w.])' + re.escape(n) + r'(?![\w])', m[cap]['body']) is not None
        print(f'  {mod}: {n}  在源decls={in_decls}  在集成body={in_body}')
    print(f'    该模块被谁import: {[r for r,v in m.items() if mod in v["imports"]]}')