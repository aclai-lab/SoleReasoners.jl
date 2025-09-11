using SoleReasoners
using Documenter

DocMeta.setdocmeta!(SoleReasoners, :DocTestSetup, :(using SoleReasoners); recursive = true)

makedocs(;
    modules = [SoleReasoners],
    authors = "Alberto Paparella",
    repo=Documenter.Remotes.GitHub("aclai-lab", "SoleReasoners.jl"),
    sitename = "SoleReasoners.jl",
    format = Documenter.HTML(;
        size_threshold = 4000000,
        prettyurls = get(ENV, "CI", "false") == "true",
        canonical = "https://aclai-lab.github.io/SoleReasoners.jl",
        assets = String[],
    ),
    pages = [
        "Home" => "index.md",
        "Getting started" => "getting-started.md",
        "Abstract Tableau" => "abstract-tableau.md",
        "Metric Heap" => "metric-heap.md",
        "Many-Valued Multi-Modal Logic" => "many-valued-multi-modal-logic.md",
        "Many-Valued Multi-Modal Tableau" => "many-valued-multi-modal-tableau.md",
        # "Examples" => "examples.md",
        ],
    # NOTE: warning
    warnonly = :true,
)

@info "`makedocs` has finished running. "

deploydocs(;
    repo = "github.com/aclai-lab/SoleReasoners.jl",
    devbranch = "main",
    target = "build",
    branch = "gh-pages",
    versions=["main" => "main", "stable" => "v^", "v#.#", "dev" => "dev"],
)
