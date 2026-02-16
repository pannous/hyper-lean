-- Darts and a Point: Throwing a dart at a dartboard (modeled as a continuous surface),
-- the probability of hitting any specific point on the board is usually zero,
-- though the dart will certainly land somewhere.

-- Using Hyperreal numbers, we can model the probability of hitting a point on the board as an infinitesimal value,
-- which is a non-zero value that is smaller than any positive real number.
-- The probability of hitting an individual point in a cirle with radius r becomes ε²/π*r²
-- The probability of hitting an line in a cirle with radius r becomes
-- a) cos(πh/2r)*ε/π*r where h is the offset from the center of the circle [2cos(πh/2r)/2π*r] OR
-- b) 2√(r²-h²)*ε/π*r where h is the offset from the top of the circle

-- proof:

import Hyper.HyperGeneral
import Mathlib.Data.Real.Basic
