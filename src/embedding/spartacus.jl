using SoleLogics: SyntaxBranch

isspartacusinstalled() = isfile(joinpath(@__DIR__, "spartacus/spartacus"))

function installspartacus()
    if !isspartacusinstalled()
        println("Installing Spartacus")
        run(`sh $(joinpath(@__DIR__, "install_spartacus.sh")) $(@__DIR__)`)
    end
end

function soletospartacus(φ::SyntaxBranch)
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

function ssat(φ::SyntaxBranch)
    b = IOBuffer()
    s = joinpath(@__DIR__, "spartacus/spartacus")
    run(
        pipeline(
            `$s --formula="$(soletospartacus(φ))"`,
            stdout = b
        )
    )
    r = take!(b) 
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
sunsat(φ::SyntaxBranch) = !ssat(φ)
sval(φ::SyntaxBranch) = sunsat(¬(φ))
sunval(φ::SyntaxBranch) = !sval(φ)
seqv(φ::SyntaxBranch, ψ::SyntaxBranch) = sval(∧(→(φ, ψ), →(ψ, φ)))  # φ <=> ψ
sent(φ::SyntaxBranch, ψ::SyntaxBranch) = sval(→(φ, ψ))  # φ => ψ
