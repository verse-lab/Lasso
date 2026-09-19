/-
  Every test under `LTLtoTGBA/Tests/`, so `lake build LTLLib.TGBABased.LTLtoTGBA.Tests` runs the whole suite at once.
  Not imported by `LTLLib.lean`, the tests check this folder and are not part of the library.
  Each test prints one line per property plus a final `PASS`/`FAIL`.
-/
import LTLLib.TGBABased.LTLtoTGBA.Tests.ConcreteVWAATests
import LTLLib.TGBABased.LTLtoTGBA.Tests.EvalTests
import LTLLib.TGBABased.LTLtoTGBA.Tests.GenTests
import LTLLib.TGBABased.LTLtoTGBA.Tests.LabelTests
import LTLLib.TGBABased.LTLtoTGBA.Tests.PipelineTests
import LTLLib.TGBABased.LTLtoTGBA.Tests.PreprocessTests
import LTLLib.TGBABased.LTLtoTGBA.Tests.VWAATests
