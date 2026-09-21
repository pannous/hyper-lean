import math
import unittest

from tube_transport.acoustics import simulate_periodic_line
from tube_transport.model import (
    ATM_PA,
    Air,
    FlowPath,
    Geometry,
    blockage_ratio,
    compliant_station,
    evaluate_flow,
    isentropic_mass_flux,
    required_effective_area_for_pressure_limit,
)


class ModelTests(unittest.TestCase):
    def setUp(self):
        self.air = Air()
        self.geometry = Geometry(1.5, 2.0, 5.0)

    def test_blockage_ratio(self):
        self.assertAlmostEqual(blockage_ratio(1.5, 2.0), 0.5625)
        self.assertAlmostEqual(self.geometry.blockage, 0.5625)

    def test_choked_mass_flux_scales_with_pressure(self):
        g1, mach1, choked1, _ = isentropic_mass_flux(2000.0, 500.0, self.air)
        g2, mach2, choked2, _ = isentropic_mass_flux(4000.0, 1000.0, self.air)
        self.assertTrue(choked1 and choked2)
        self.assertEqual(mach1, 1.0)
        self.assertEqual(mach2, 1.0)
        self.assertAlmostEqual(g2 / g1, 2.0)

    def test_flow_solution_conserves_mass_and_power(self):
        path = FlowPath("annulus", self.geometry.annulus_area_m2, 0.82)
        result = evaluate_flow(self.geometry, 150.0, 0.01 * ATM_PA, [path], self.air)
        self.assertLess(result.mass_conservation_relative_error, 1e-10)
        self.assertLess(result.power_conservation_relative_error, 1e-12)
        self.assertGreater(result.pressure_front_pa, result.pressure_rear_pa)

    def test_pressure_ratio_is_ideal_gas_pressure_independent(self):
        path = FlowPath("annulus", self.geometry.annulus_area_m2, 0.82)
        low = evaluate_flow(self.geometry, 150.0, 0.001 * ATM_PA, [path], self.air)
        high = evaluate_flow(self.geometry, 150.0, 0.1 * ATM_PA, [path], self.air)
        self.assertAlmostEqual(low.pressure_ratio, high.pressure_ratio, places=10)
        self.assertAlmostEqual(high.mass_flow_kg_s / low.mass_flow_kg_s, 100.0, places=8)

    def test_more_allowed_delta_p_needs_less_area(self):
        rho = self.air.density(0.01 * ATM_PA)
        mdot = rho * self.geometry.pod_area_m2 * 200.0
        tight = required_effective_area_for_pressure_limit(mdot, 0.01 * ATM_PA, 0.02, self.air)
        loose = required_effective_area_for_pressure_limit(mdot, 0.01 * ATM_PA, 0.10, self.air)
        self.assertGreater(tight, loose)

    def test_compliant_volume_conservation(self):
        station = compliant_station(self.geometry, 10.0, 0.01 * ATM_PA, 0.05, 0.1, self.air)
        self.assertAlmostEqual(
            station["swept_volume_per_station_m3"], self.geometry.pod_area_m2 * 10.0
        )
        self.assertAlmostEqual(
            station["swept_volume_per_vehicle_km_m3"], self.geometry.pod_area_m2 * 1000.0
        )

    def test_acoustic_source_sink_conserves_volume(self):
        result = simulate_periodic_line(
            self.geometry, 100.0, 0.01 * ATM_PA,
            duration_s=0.04, line_length_m=100.0, cells=100, air=self.air,
        )
        self.assertLess(result.mass_balance_equivalent_m3, 1e-9)
        self.assertTrue(math.isfinite(float(result.peak_pressure_pa[-1])))


if __name__ == "__main__":
    unittest.main()
