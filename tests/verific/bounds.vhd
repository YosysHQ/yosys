library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity work is
    Port (
        a : in INTEGER range -5 to 10;
        b : out INTEGER range -6 to 11
    );
end entity work;

architecture Behavioral of work is
begin
    process(a)
    begin
        b <= a;
    end process;
end architecture Behavioral;
