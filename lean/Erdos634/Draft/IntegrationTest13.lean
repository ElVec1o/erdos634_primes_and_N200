-- Draft/IntegrationTest13.lean — integration test: the three row-3 witness files compile together as a unit.
--
-- Dependency chain: FluxGRow3WitnessFinal depends on FluxGRow3WitnessBridge depends on
-- FluxGRow3AngleWitnessDissection. All three are imported explicitly for clarity.
import Erdos634.Draft.FluxGRow3AngleWitnessDissection
import Erdos634.Draft.FluxGRow3WitnessBridge
import Erdos634.Draft.FluxGRow3WitnessFinal
