-- `HyperReals.factorial` (the module this once imported) no longer exists —
-- `Hyper.HyperReal` is now `abbrev HyperReal := HyperList` (see
-- Hyper/HyperReal.lean). Its Taylor-series intent lives on as `factQ` in
-- Hyper/HyperTranscendental.lean, the exact-ℚ factorial used by `hexp`/
-- `hsin`/`hcos`.
import Hyper.HyperTranscendental
open Hypers.HyperLists

#eval factQ 0
#eval factQ 2
#eval factQ 4
