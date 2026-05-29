# Language MPC Schemas

This example defines public object schemas with secret-typed fields that describe an MPC job
request, then builds nested review metadata with `List[List[int64]]` and
`Dict[string, List[int64]]`. User-defined objects are currently schema
declarations used by the compiler and tooling; dynamic runtime instances are
represented with `create_object` in other examples.
