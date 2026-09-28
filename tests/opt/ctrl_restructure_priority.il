module \ctrl_restructure_priority
  wire input 1 \clk
  wire input 2 \enable
  wire input 3 \reset
  wire input 4 \update
  wire width 8 input 5 \a
  wire width 8 output 6 \q
  wire width 8 \d
  cell $mux \data_mux
    parameter \WIDTH 8
    connect \A \q
    connect \B \a
    connect \S \update
    connect \Y \d
  end
  cell $sdffce \state
    parameter \WIDTH 8
    parameter \CLK_POLARITY 1
    parameter \EN_POLARITY 1
    parameter \SRST_POLARITY 1
    parameter \SRST_VALUE 8'00110101
    connect \CLK \clk
    connect \EN \enable
    connect \SRST \reset
    connect \D \d
    connect \Q \q
  end
end
