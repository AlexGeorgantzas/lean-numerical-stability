# R12 routing and retention

The frozen route map moves 34 public declarations from three source owners into
six semantic leaves: Equation23 ProductBounds PointRow (3), Equation25
BackwardError Bounds (2), Equation25 PartitionedComputation Implementation1
(1), Table01 BackwardErrorBounds Endpoints (8), Table01 DiagonalDominance
Bounds (15), and Table01 ProductTransfers Families (5).

Declaration names, namespaces, kinds, visibility, types, attributes, and
proof/bodies are preserved exactly. Physical source order is retained inside
each leaf so dependencies remain valid, while DECLARATION_ROUTES.tsv remains
byte-identical to the name-sorted frozen control artifact.

Equation23.lean, Equation25.lean, and Table01.lean are documented, sorted,
unique, declaration-free complete aggregates over every existing and new exact
child. No historical path is deleted or renamed. RETENTION.tsv records all 34
names as present exactly once.
