import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
from port_v2 import port_one, analyze, v2_index

# 域分配：读文件内容判断（按关键词）
def guess_domain(name):
    import re
    from port_v2 import find_legacy
    p = find_legacy(name)
    t = open(p, encoding='utf-8').read()[:6000]
    if re.search(r'backdoor|frontdoor|d-?sep|DSep|因果|干预|do\(|反事实|abduction|identifiab', t, re.I): return 'Predict'
    if re.search(r'误差|拟合|sigma|σ|Lipschitz|ErrorBound|Gauss', t, re.I): return 'Error'
    if re.search(r'FCA|概念格|蕴含|形式背景|LawRule|规则层', t, re.I): return 'Rules'
    if re.search(r'收敛|闭环|converge|回写|残差|writeBack|Optimal', t, re.I): return 'Loop'
    if re.search(r'SCM|结构方程|建模|观测|外生|Pearl|马尔可夫|Markov', t, re.I): return 'Modeling'
    if re.search(r'轨迹|Trajectory|时态|时间|Time', t, re.I): return 'Model'
    if re.search(r'模态|导出|Modality|Export|View', t, re.I): return 'Export'
    return 'Meta'

if __name__ == '__main__':
    v2m = v2_index()
    rows = []
    for dp, _, fs in os.walk(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'FateWorld', 'Legacy')):
        for f in fs:
            if not f.endswith('.lean'): continue
            n = f[:-5]
            if n in v2m: continue
            info = analyze(n)
            if info and not info['unresolved'] and not info['blocked'] and info['theorems'] > 0:
                rows.append(info)
    rows.sort(key=lambda r: -r['theorems'])
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else len(rows)
    ok = fail = 0
    for r in rows[:limit]:
        d = guess_domain(r['name'])
        res = port_one(r['name'], d)
        if res['ok']:
            ok += 1
            print(f'[OK  ] {r["name"]:<28} → {d}', flush=True)
        else:
            fail += 1
            print(f'[FAIL] {r["name"]:<28} {res.get("why")}', flush=True)
    print(f'\n成功 {ok} / 失败 {fail}')