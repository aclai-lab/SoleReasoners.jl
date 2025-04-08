using StatsBase: countmap

"""
    roundrobin!(metricheaps::Vector{MetricHeap}, cycle::Int)

Choose a node using the provided `MetricHeap`s, alternating between them at each
`cycle`.

The result can either be nothing, in case all heaps are empty and therefore the
tableau closed, or a node; an expanded node can only be returned if it is a leaf
and in that case it represents a satisfiable branch for the tableau (i.e., a
fully expanded open branch without contraddictions).

This is the default and suggested policy, as it prevents starvation.
"""
function roundrobin!(metricheaps::Vector{MetricHeap}, cycle::Int)
    counter = length(metricheaps) - 1
    node = nothing
    while counter != length(metricheaps)
        metricheap = metricheaps[((cycle + counter) % length(metricheaps)) + 1]
        while !isempty(metricheap)
            node = pop!(metricheap)
            if closed(node)
                continue
            elseif expanded(node)
                if isleaf(node)
                    return node # found a satisfiable branch
                else
                    continue
                end
            else
                return node
            end
        end
        counter += 1    # the heap is empty, try the next heap
    end
    return nothing  # all heaps are empty, hence the tableau is closed
end

"""
    mostvoted!(metricheaps::Vector{MetricHeap}, args...)

Choose a leaf using the provided `MetricHeap`s, returning the leaf which is the
head of most of the heaps. In case

To prevent starvation, use [`roundrobin`](@ref) instead.
"""
function mostvoted!(metricheaps::Vector{MetricHeap}, args...)
    candidates = Vector{AbstractTableau}()
    for metricheap ∈ metricheaps
        while !isempty(metricheap)
            head = tableau(first(heap(metricheap)))
            if closed(head)
                pop!(metricheap)
                continue
            elseif expanded(head)
                if isleaf(head)
                    return head # found a satisfiable branch
                else
                    pop!(metricheap)
                    continue
                end
            else
                push!(candidates, head)
                break
            end
        end
    end
    candidatesdict = countmap(candidates)
    if isempty(candidatesdict)
        return nothing  # all heaps are empty, hence the tableau is closed
    else
        return collect(
            keys(candidatesdict)
        )[
            argmax(collect(values(candidatesdict)))
        ]
    end
end
