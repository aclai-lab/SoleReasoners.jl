# Metric Heap

This folder contains the necessary components for the search strategies
allowing for a ``smarter'' way of expanding the tableau tree structure,
aiming at finding a fully expanded open branch (resp. closing all branches)
in the fastest way possible.

A `MetricHeap` is basically a heap parametrized over a metric, i.e., a function
which extracts some information about a tableau branch, therefore containing in
each node a tableau branch and the relative value for the metric, and which is 
ordered as a min heap over this metric value.

Helpers to clear the heaps (e.g., to deallocate memory removing already expanded
non-leaf nodes and closed nodes) are also provided.
