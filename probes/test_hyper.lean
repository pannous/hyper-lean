-- `Hyper.Hyper` (the module this once imported) — a fixed 3-slot
-- `real_part`/`epsilon_part`/`infinite_part`/`exceptional` struct — was
-- deliberately gutted in commit 8a42866 in favor of the general `R*` =
-- `List (ℚ × ℚ)` model in Hyper/HyperList.lean. `.real_part` is now `st`
-- (the standard-part function), which works on any `R*` value, not just a
-- fixed 3-term shape.
import Hyper.HyperReal

open Hypers

#check (ε : R*)
#check (ω : R*)
#check (ε * ω : R*)

#eval st (1 : R*)
