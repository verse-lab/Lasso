/-
  Every test under `TGBABased/Tests/`, so `lake build LTLLib.TGBABased.Tests` runs the whole suite at once.
  Not imported by `LTLLib.lean`, the tests are a check on the library rather than part of it.

  Each executable test prints one line per property plus a final `PASS`/`FAIL`. `PipelineTheorems` instead
  checks at elaboration time, so a regression there fails the build.
-/
import LTLLib.TGBABased.Tests.EdgeLabels
import LTLLib.TGBABased.Tests.EntryEdgeMarks
import LTLLib.TGBABased.Tests.FairClass
import LTLLib.TGBABased.Tests.FairNormalForm
import LTLLib.TGBABased.Tests.FairOptions
import LTLLib.TGBABased.Tests.FairPreprocess
import LTLLib.TGBABased.Tests.FairRouter
import LTLLib.TGBABased.Tests.ModelCheckCounterExample
import LTLLib.TGBABased.Tests.PipelineTheorems
import LTLLib.TGBABased.Tests.PruneJointRegions
import LTLLib.TGBABased.Tests.RegionLatch
import LTLLib.TGBABased.Tests.RestrictedConnector
import LTLLib.TGBABased.Tests.SCCEnumeration
import LTLLib.TGBABased.Tests.StreettPrune
import LTLLib.TGBABased.Tests.TarjanSCC
import LTLLib.TGBABased.Tests.WeakFairness
import LTLLib.TGBABased.Tests.WitnessStress
import LTLLib.TGBABased.Tests.ZeroMarks
