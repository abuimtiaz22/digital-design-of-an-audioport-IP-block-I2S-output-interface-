-------------------------------------------------------------------------------
-- i2s_unit.vhd:  VHDL RTL model for the i2s_unit.
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-------------------------------------------------------------------------------
-- Entity declaration
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity i2s_unit is
    port (
        clk       : in std_logic;
        rst_n     : in std_logic;
        play_in   : in std_logic;
        tick_in   : in std_logic;
        audio0_in : in std_logic_vector(23 downto 0);
        audio1_in : in std_logic_vector(23 downto 0);    
        req_out   : out std_logic;
        ws_out    : out std_logic;
        sck_out   : out std_logic;
        sdo_out   : out std_logic
    );
end i2s_unit;
-------------------------------------------------------------------------------
-- Architecture declaration
-------------------------------------------------------------------------------
architecture RTL of i2s_unit is

    -- Registers
    signal counter      : unsigned(8 downto 0);
    signal shift_reg    : std_logic_vector(47 downto 0);
    signal input_reg    : std_logic_vector(47 downto 0);
    signal play_r       : std_logic;

    -- Control Signals
    signal load_enable  : std_logic;
    signal shift_enable : std_logic;
    signal ws_out_logic : std_logic;
    signal sck_out_logic : std_logic;
    signal end_s : std_logic;


begin

    sck_out <= sck_out_logic when play_r = '1' else '0';
    ws_out  <= ws_out_logic when play_r = '1' else '0';
    sdo_out <= shift_reg(47) when play_r = '1' else '0';
    

-- Mode Management
    process (clk, rst_n)

   begin
    if rst_n = '0' then
        play_r <= '0';
    elsif rising_edge(clk) then
        if (play_r = '1') and (play_in = '0') and (end_s = '1') then
            play_r <= '0';
        elsif play_in = '1' then
            play_r <= '1';
        end if;
    end if;
end process;

    -- Counter Logic
    process (clk, rst_n)
    begin
    if rst_n = '0' then
        counter <= (others => '0');
    elsif rising_edge(clk) then
        if play_r = '1' then
            if counter = 383 then
                counter <= (others => '0');
            else
                counter <= counter + 1;
            end if;
        else
            counter <= (others => '0');
        end if;
    end if;
end process;


     -- Input Register Logic
    process (clk, rst_n)
   begin
    if rst_n = '0' then
        input_reg <= (others => '0');
    elsif rising_edge(clk) then
        if tick_in = '1' and play_r = '1' then
            input_reg <= audio0_in & audio1_in;
        elsif play_r = '0' then
            input_reg <= (others => '0');
        end if;
    end if;
end process;

-- Shift Register Logic
process(clk, rst_n)
begin
    if rst_n = '0' then
        shift_reg <= (others => '0');
    elsif rising_edge(clk) then
        if play_r = '1' then
            if load_enable = '1' then
                shift_reg <= input_reg;
            elsif shift_enable = '1' then
                shift_reg <= shift_reg(46 downto 0) & '0';
            end if;
        else
            shift_reg <= (others => '0');
        end if;
    end if;
end process;

--Combinational Logic
process(counter)
begin
    req_out     <= '0';
    load_enable        <= '0';
    end_s     <= '0';
    shift_enable       <= '0';
    ws_out_logic  <= '0';
    sck_out_logic <= '0';

    if counter = 3 then
        req_out <= '1';
        load_enable    <= '1';
    end if;

    if counter = 7 then
        end_s <= '1';
    end if;

    if counter = 11 or (counter > 11 and (to_integer(counter) - 11) mod 8 = 0 and counter <= 383) then
        shift_enable <= '1';
    end if;

    if counter > 187 and counter < 380 then
        ws_out_logic <= '1';
    end if;

    if (to_integer(counter) mod 8) < 4 then
        sck_out_logic <= '1';
    else
        sck_out_logic <= '0';
    end if;
end process;

end RTL;
