-- This module serves as the root of the `Zcash` library: its sole import root, so
-- `lake build Zcash` is exactly this file's transitive closure. No module imports it — it is a
-- build entry point, not a re-export surface — and the line it draws is between the parametric
-- library and anything pinned to a concrete capture, which lives in the `FixtureCheck`,
-- `CircuitCheck`, `MetaCheck`, and `SecurityCheck` targets instead.
--
-- Import modules here that should be built as part of the library. Note that this list is not
-- the whole story for the SNARK soundness stack: `Zcash/Snark.lean` deliberately does not
-- re-export `Soundness/` or the rational-match tier (the byte-locked fixture
-- captures must `import Zcash.Snark`, so whatever that umbrella re-exports lands on their build
-- path). Those modules enter this closure through the census imports in `Zcash.TrustBoundary`,
-- with a `lakefile.toml` glob as the backstop should that ever stop being true;
-- `scripts/check_build_coverage.sh` asserts in CI that every module file in the package is
-- reachable from some default target.

import Zcash.Common
import Zcash.Coppice
import Zcash.Circuits
import Zcash.Circuits.Integration
import Zcash.Security
import Zcash.Snark
import Zcash.TrustBoundary
