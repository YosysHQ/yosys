library ieee;
use ieee.std_logic_1164.all;

entity demo is
	port (
		clock : in std_logic;
		ctrl : in std_logic;
		x : out std_logic
	);
end entity;

architecture rtl of demo is
	signal read : std_logic;
	signal write : std_logic;
	signal ready : std_logic;
begin
	process (clock) begin
		if (rising_edge(clock)) then
			read <= not ctrl;
			write <= ctrl;
			ready <= write;
		end if;
	end process;

	x <= read xor write xor ready;
end architecture;
