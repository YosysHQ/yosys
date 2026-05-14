library ieee;
use ieee.std_logic_1164.all;

entity vhdl_mod is
	port (
		a : in std_logic;
		y : out std_logic
	);
end entity vhdl_mod;

architecture rtl of vhdl_mod is
begin
	y <= a;
end architecture rtl;
