import csv, os
ROOT = r'C:\Users\xingg\Desktop\命运计划\Fate-world-prediction'
rows = list(csv.DictReader(open(os.path.join(ROOT, '_inventory', '引用图.csv'), encoding='utf-8-sig')))
targets = ['Modeling.CausBayesBall', 'Modeling.CFMap', 'Modeling.FiniteCondIndep',
           'Modeling.CondIndepGeneralNZ', 'Modeling.CondIndepSemigraphoid',
           'Rules.T112SecondQuotient', 'Export.Carrier']
for r in rows:
    if r['模块'] in targets:
        print(f"  {r['模块']:<42} {r['状态']:<6} 被import{r['被import']:>3} 被真消费{r['被真消费']:>3}")