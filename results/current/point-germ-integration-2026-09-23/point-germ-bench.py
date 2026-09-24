import json, statistics, time
from pathlib import Path
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm
rows=[]
for n in (16,32,64,128,256,512,1024):
    for mode in ('endpoint-result', 'point-germ'):
        cold=[]; warm=[]; counters=[]
        for _ in range(5):
            term=AntihydraArithmeticTerm(n)
            start=time.perf_counter_ns()
            value=(term.result().h>>2)&1 if mode=='endpoint-result' else term.digit(2)
            cold.append(time.perf_counter_ns()-start)
            start=time.perf_counter_ns()
            again=(term.result().h>>2)&1 if mode=='endpoint-result' else term.digit(2)
            warm.append(time.perf_counter_ns()-start)
            assert again==value
            counters.append(dict(term.ledger.counters))
            term.arithmetic_workspace.dispose()
        rows.append(dict(steps=n,route=mode,trials=5,cold_ns=cold,warm_ns=warm,
                         cold_median_ns=statistics.median(cold),warm_median_ns=statistics.median(warm),counters=counters))
Path('/tmp/point-germ-bench.json').write_text(json.dumps(rows,indent=2))
for row in rows:
    print(row['steps'],row['route'],'cold_ms',round(row['cold_median_ns']/1e6,3),'warm_ms',round(row['warm_median_ns']/1e6,3))
