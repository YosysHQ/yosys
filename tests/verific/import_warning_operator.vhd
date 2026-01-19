library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity top is
    Port (
        a   : in  STD_LOGIC_VECTOR(3 downto 0);
        b   : in  STD_LOGIC_VECTOR(3 downto 0);
        y   : out STD_LOGIC_VECTOR(3 downto 0)
    );
end top;

architecture Behavioral of top is
begin
    y <= a nor b;
end Behavioral;
