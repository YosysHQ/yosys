library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;

entity top is
	port (
		clk : in std_logic;
		rst : in std_logic;
		up : in std_logic;
		down : in std_logic;
		cnt : buffer std_logic_vector(7 downto 0)
	);
end entity;

architecture rtl of top is
begin
	process (clk) begin
		if rising_edge(clk) then
			if rst = '1' then
				cnt <= std_logic_vector(to_unsigned(0, 8));
			elsif up = '1' then
				cnt <= cnt + std_logic_vector(to_unsigned(1, 8));
			elsif down = '1' then
				cnt <= cnt - std_logic_vector(to_unsigned(1, 8));
			end if;
		end if;
	end process;

	-- PSL default clock is (rising_edge(clk));
	-- PSL assume always ( down -> not up );
	-- PSL assert always ( up |=> (cnt = prev(cnt) + std_logic_vector(to_unsigned(1, 8))) ) abort rst = '1';
	-- PSL assert always ( down |=> (cnt = prev(cnt) - std_logic_vector(to_unsigned(1, 8))) ) abort rst = '1';
end architecture;
