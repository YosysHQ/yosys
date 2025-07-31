module \m_a
    wire input 1 \w_i
    wire output 2 \w_o
    connect \w_o \w_i
end

module \m_b
    wire input 1 \w_i
    wire output 2 \w_o
end

attribute \top 1
module \top
    attribute \raise_error 3
    wire \w_a
    wire \w_b
    wire \w_c

    cell \m_a \c_a
        connect \w_i \w_a
        connect \w_o \w_b
    end

    cell \m_a \c_b
        connect \w_i \w_b
        connect \w_o \w_c
    end

    cell \m_b \c_c
        connect \w_i \w_c
        connect \w_o \w_a
    end

    cell \m_b \c_d
        connect \w_i 1'0
        connect \w_o 1'1
    end
end
