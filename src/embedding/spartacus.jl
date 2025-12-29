using UUIDs
using SoleLogics: Atom, BooleanTruth, SyntaxBranch

isspartacusinstalled() = isfile(joinpath(@__DIR__, "spartacus/spartacus"))

function installspartacus()
    if !isspartacusinstalled()
        println("Installing Spartacus")
        run(`sh $(joinpath(@__DIR__, "install_spartacus.sh")) $(@__DIR__)`)
    end
end

function soletospartacus(φ::Union{Atom, BooleanTruth, SyntaxBranch})
    s = syntaxstring(φ)
    r = Vector{Char}()
    for c in s
        if c == '¬'
            push!(r, '~')
        elseif c == '∧'
            push!(r, '&')
        elseif c == '∨'
            push!(r, '|')
        elseif c == '→'
            push!(r, '-', '>')
        elseif c == '◊'
            push!(r, '<', 'a', '>')
        elseif c == '□'
            push!(r, '[', 'a', ']')
        elseif c == '⊤'
            push!(r, '1')
        elseif c == '⊥'
            push!(r, '0')
        else
            push!(r, c)
        end
    end
    return String(r)
end

function ssat(φ::Union{Atom, BooleanTruth, SyntaxBranch}; timeout::Union{Nothing, Int} = nothing)
    b = IOBuffer()
    s = joinpath(@__DIR__, "spartacus/spartacus")
    uuid = UUIDs.uuid4()
    filepath = "$(tempdir())/temp$uuid"
    touch(filepath)
    open(filepath, "w") do file
        write(file, soletospartacus(φ))
    end
    if isnothing(timeout)
        run(
            pipeline(
                `$s --file="$filepath"`,
                stdout = b
            )
        )
        r = take!(b) 
    else
        run(
            pipeline(
                `$s --file="$filepath" --timeout=$timeout`,
                stdout = b
            )
        )
        r = take!(b)
        if r[lastindex(r)-7:lastindex(r)] == UInt8[
            0x54,
            0x69,
            0x6d,
            0x65,
            0x6f,
            0x75,
            0x74,
            0x0a
        ]
            @warn "Timeout\n"
            return nothing  # timeout
        end
    end
    rm(filepath)
    return r[lastindex(r)-12:lastindex(r)] == UInt8[
        0x0a,
        0x73,
        0x61,
        0x74,
        0x69,
        0x73,
        0x66,
        0x69,
        0x61,
        0x62,
        0x6c,
        0x65,
        0x0a
    ]
end
sunsat(φ::Union{Atom, BooleanTruth, SyntaxBranch}) = !ssat(φ)
sval(φ::Union{Atom, BooleanTruth, SyntaxBranch}) = sunsat(¬(φ))
sunval(φ::Union{Atom, BooleanTruth, SyntaxBranch}) = !sval(φ)
seqv(φ::Union{Atom, BooleanTruth, SyntaxBranch}, ψ::Union{Atom, BooleanTruth, SyntaxBranch}) = sval(∧(→(φ, ψ), →(ψ, φ)))  # φ <=> ψ
sent(φ::Union{Atom, BooleanTruth, SyntaxBranch}, ψ::Union{Atom, BooleanTruth, SyntaxBranch}) = sval(→(φ, ψ))  # φ => ψ
