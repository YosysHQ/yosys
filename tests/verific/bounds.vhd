library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity test is
    Port (
        -- BIT type
        bit_in : in BIT;
        bit_out : out BIT;

        -- BIT_VECTOR type
        bit_vector_in : in BIT_VECTOR(3 downto 0);
        bit_vector_out : out BIT_VECTOR(3 downto 0);

        -- BIT_VECTOR type with to index
        bit_vector_in_to : in BIT_VECTOR(0 to 3);
        bit_vector_out_to : out BIT_VECTOR(0 to 3);

        -- STD_ULOGIC type
        std_ulogic_in : in STD_ULOGIC;
        std_ulogic_out : out STD_ULOGIC;

        -- STD_ULOGIC_VECTOR type
        std_ulogic_vector_in : in STD_ULOGIC_VECTOR(3 downto 0);
        std_ulogic_vector_out : out STD_ULOGIC_VECTOR(3 downto 0);

        -- STD_ULOGIC_VECTOR type with to index
        std_ulogic_vector_in_to : in STD_ULOGIC_VECTOR(0 to 3);
        std_ulogic_vector_out_to : out STD_ULOGIC_VECTOR(0 to 3);

        -- STD_LOGIC type
        std_logic_in : in STD_LOGIC;
        std_logic_out : out STD_LOGIC;

        -- STD_LOGIC_VECTOR type
        std_logic_vector_in : in STD_LOGIC_VECTOR(3 downto 0);
        std_logic_vector_out : out STD_LOGIC_VECTOR(3 downto 0);

        -- STD_LOGIC_VECTOR type with to index
        std_logic_vector_in_to : in STD_LOGIC_VECTOR(0 to 3);
        std_logic_vector_out_to : out STD_LOGIC_VECTOR(0 to 3);

        -- SIGNED type
        signed_in : in SIGNED(3 downto 0);
        signed_out : out SIGNED(3 downto 0);

        -- SIGNED type with to index
        signed_in_to : in SIGNED(0 to 3);
        signed_out_to : out SIGNED(0 to 3);

        -- UNSIGNED type
        unsigned_in : in UNSIGNED(3 downto 0);
        unsigned_out : out UNSIGNED(3 downto 0);

        -- UNSIGNED type with to index
        unsigned_in_to : in UNSIGNED(0 to 3);
        unsigned_out_to : out UNSIGNED(0 to 3);

        -- INTEGER type without range
        integer_in : in INTEGER;
        integer_out : out INTEGER;

        -- INTEGER type with range
        integer_with_range_in : in INTEGER range -5 to 10;
        integer_with_range_out : out INTEGER range -6 to 10;

        -- INTEGER type with single value range
        integer_single_value_in : in INTEGER range 5 to 5;
        integer_single_value_out : out INTEGER range 5 to 5;

        -- INTEGER type with null range
        integer_null_range_in : in INTEGER range 7 to -1;
        integer_null_range_out : out INTEGER range 0 to -1;

        -- NATURAL type
        natural_in : in NATURAL;
        natural_out : out NATURAL;
 
        -- POSITIVE type
        positive_in : in POSITIVE;
        positive_out : out POSITIVE
    );
end entity test;

architecture Behavioral of test is
    signal integer_with_range : INTEGER range -1 to 100;
begin
    bit_out <= bit_in;
    bit_vector_out <= bit_vector_in;
    bit_vector_out_to <= bit_vector_in_to;
    std_ulogic_out <= std_ulogic_in;
    std_ulogic_vector_out <= std_ulogic_vector_in;
    std_ulogic_vector_out_to <= std_ulogic_vector_in_to;
    std_logic_out <= std_logic_in;
    std_logic_vector_out <= std_logic_vector_in;
    std_logic_vector_out_to <= std_logic_vector_in_to;
    signed_out <= signed_in;
    signed_out_to <= signed_in_to;
    unsigned_out <= unsigned_in;
    unsigned_out_to <= unsigned_in_to;
    integer_with_range_out <= integer_with_range_in;
    integer_out <= integer_in;
    integer_single_value_out <= integer_single_value_in;
    integer_null_range_out <= integer_null_range_in;
    natural_out <= natural_in;
    positive_out <= positive_in;

    integer_with_range <= 42;
end architecture Behavioral;
