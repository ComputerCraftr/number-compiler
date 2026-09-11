# Compressed-word cascade evaluation

Exact one-step bimachine evaluation over a hash-consed SLP; no input word is materialized during the transform.

|steps|word length|reachable SLP nodes|arena nodes|block-section memo|last step sec|
|---:|---:|---:|---:|---:|---:|
|1|4|7|13|7|0.000044|
|2|4|7|19|14|0.000025|
|4|5|9|29|28|0.000024|
|8|6|10|48|60|0.000024|
|16|7|13|90|145|0.000022|
|32|10|18|195|377|0.000030|
|64|18|28|552|1134|0.000054|
|128|31|46|1934|3790|0.000072|
|256|59|77|7210|11814|0.000146|

This is an exact spatial cascade/section engine.  It removes per-digit scans when repeated SLP blocks exist, but sequentially applying the one-step operator is still linear in temporal step count; a powered section rewrite is required for full J.
