import AnalyticNumberTheory.Dirichlet.TwistedSmoothedPerronRight

/-!
# Public axiom audit extension for the smoothed Perron API

`Audit.lean` predates the consumer-driven Dirichlet extraction and is intentionally large.
This small companion keeps the new public Perron theorems under the same exact CI axiom
whitelist without duplicating the repository-wide audit source.
-/

#print axioms AnalyticNumberTheory.Dirichlet.twistedSmoothedPerron
#print axioms AnalyticNumberTheory.Dirichlet.twistedSmoothedPerronIntegrand_integrable_right
#print axioms AnalyticNumberTheory.Dirichlet.twistedSmoothedPerron_verticalIntegral_split_three
