definition module rule

from graph import Graph,Node

// --- Exported types

:: Rule sym var
:: Rgraph sym var

// --- Functions on rules

// Build a rule from its constituents
mkrule :: [.var] .var (Graph .sym .var) -> Rule .sym .var

// The arguments of a rule, i.e. the roots of its lhs
arguments :: !(Rule .sym .var) -> [.var]

// The root of a rule, i.e. of its rhs
ruleroot :: !(Rule .sym .var) -> .var

// The graph part of a rule, i.e. its bindings
rulegraph :: !(Rule .sym .var) -> Graph .sym .var

// --- Functions on rooted graphs

// The empty rooted graph with a given root
emptyrgraph  :: .var -> Rgraph .sym .var

// Update the contents of a variable in a rooted graph
updatergraph :: .var (Node .sym .var) !(Rgraph .sym .var) -> Rgraph .sym .var

// Prune a rooted graph at a variable (making it free)
prunergraph  :: .var !(Rgraph .sym .var) -> Rgraph .sym .var

// Get the root of a rooted graph
rgraphroot   :: !(Rgraph .sym .var) -> .var

// Get the graph part of a rooted graph
rgraphgraph  :: !(Rgraph .sym .var) -> Graph .sym .var

// Build a rooted graph from a root and a graph
mkrgraph     :: .var (Graph .sym .var) -> Rgraph .sym .var
