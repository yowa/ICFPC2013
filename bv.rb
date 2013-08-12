require 'json'

class Problem
  def initialize(h=nil)
    @active = true
    @h = {}
    if h.kind_of?(Hash)
      @h = h.dup
      @size = h["size"]
      @operators = h["operators"].map{|x|x.to_sym}.freeze
      @id = h["id"]
      @active = !h["solved"] && (!h["timeLeft"] || h["timeLeft"] > 0)
    elsif h.kind_of?(String)
      if (a = h.split('/')).size == 2 && 
          a[0].match(/\A\d+\z/) &&
          a[1].match(/\A\[[a-z:0-9 ,]*\]\z/)
        @h = {}
        @size = @h["size"] = a[0].to_i
        @operators = @h["operators"] = eval(a[1])
        @id = "FromString#{"%08X"%rand(2**32)}"
      end
    end
  end
  attr_accessor :size, :operators, :id, :active

  def inspect
    "#<#{@id} #{@size}/#{@operators} #{@h["solved"]}>"
  end
end

class BV
  MASK64 = 0xffffffffffffffff

  def dump(prog)
    "(lambda (x) #{dump_sub(prog)})"
  end

  def dump_sub(prog)
    return prog unless prog.kind_of?(Array)
    case (op = prog[0])
    when :not, :shl1, :shr1, :shr4, :shr16, 
      :and, :or, :xor, :plus,
      :if0
      return "(#{prog.map{|x| dump_sub(x)}*" "})"
    when :fold
      return ["(fold",
              dump_sub(prog[1]), 
              dump_sub(prog[2]),
              "(lambda",
              "(#{dump_sub(prog[3])}",
              "#{dump_sub(prog[4])})",
              "#{dump_sub(prog[5])}))"]*" "
    end
  end

  def eval(prog, arg)
    @vars = {:x => arg}
    ev(prog)
  end

  def simple(prog)
    return prog if prog.kind_of?(Numeric) || prog.kind_of?(Symbol)
    prog = prog.dup

    case prog[0]
    when :if0
      prog[1] = simple(prog[1])
      prog[2] = simple(prog[2])
      prog[3] = simple(prog[3])

      if prog[2] == prog[3]
        return prog[2]
      elsif prog[1] == 0
        return prog[2]
      elsif prog[1] == 1
        return prog[3]
      else
        return prog
      end
    when :not
      prog[1] = simple(prog[1])
      #return send(prog[0], prog[1]) if prog[1].kind_of?(Numeric)
      return prog
    when :shl1
      prog[1] = simple(prog[1])
      if prog[1] == 0
        return 0
      end

      #return send(prog[0], prog[1]) if prog[1].kind_of?(Numeric)
      #return 0 if prog[1] == 0

      return prog
    when :shr1, :shr4, :shr16
      prog[1] = simple(prog[1])
      if prog[1] == 0 || prog[1] == 1
        return 0
      end

      return prog
    when :and
      prog[1] = simple(prog[1])
      prog[2] = simple(prog[2])

      if prog[1] == 0 || prog[2] == 0
        return 0
      #elsif prog[1].kind_of?(Numeric) && prog[2].kind_of?(Numeric)
      #  return send(prog[0], prog[1], prog[2])
      elsif prog[1] == prog[2]
        return prog[1]
      else
        return prog
      end
    when :or
      prog[1] = simple(prog[1])
      prog[2] = simple(prog[2])

      return prog
    when :xor
      prog[1] = simple(prog[1])
      prog[2] = simple(prog[2])

      if prog[1] == prog[2]
        return 0
      #elsif prog[1].kind_of?(Numeric) && prog[2].kind_of?(Numeric)
      #  return send(prog[0], prog[1], prog[2])
      end

      return prog
    when :plus
      prog[1] = simple(prog[1])
      prog[2] = simple(prog[2])

      if prog[1] == 0
        return prog[2]
      elsif prog[2] == 0
        return prog[1]
      end

      return prog
    end

    return prog
  end

  private
  def ev(prog)
    if prog.kind_of?(Numeric)
      return prog
    elsif prog.kind_of?(Symbol)
      return @vars[prog]
    else
      case prog[0] 
      when :if0
        val = ev(prog[1])
        return ev((val == 0) ? prog[2] : prog[3])
      when :not, :shl1, :shr1, :shr4, :shr16
        return send(prog[0], ev(prog[1]))
      when :and, :or, :xor, :plus
        return send(prog[0], ev(prog[1]), ev(prog[2]))
      when :fold
        e0 = ev(prog[1])
        e1 = ev(prog[2])
        8.times do
          @vars[prog[3]] = e0 & 0xff
          @vars[prog[4]] = e1
          e1 = ev(prog[5])
          e0 >>= 8
        end
        return e1
      end
    end

    raise "What? #{prog.inspect}"
  end

  def fold(e0, e1, la)
    x = e0
    r = e1
    8.times do
      r = la.call(x&0xff, r)
      x >>= 8
    end
    r
  end

  def not(x)
    x ^ 0xffffffffffffffff
  end

  def shl1(x)
    (x << 1) & MASK64
  end

  def shr1(x)
    (x >> 1) & MASK64
  end

  def shr4(x)
    (x >> 4) & MASK64
  end

  def shr16(x)
    (x >> 16) & MASK64
  end

  def and(x, y)
    x&y
  end

  def or(x, y)
    x|y
  end

  def xor(x, y)
    x^y
  end

  def plus(x, y)
    (x+y)&MASK64
  end
end

if __FILE__ == $0
  bv = BV.new

  #p bv.eval([:shr1, :ARG], 3)
  #p bv.eval([:fold, :ARG, 0, :y, :z, [:or, :y, :z]], 0x1122334455667788)

  prog = [:xor, [:or, [:shr4, [:shr16, [:plus, [:shl1, :ARG], [:shl1, [:xor, [:not, [:and, [:if0, [:shr4, [:xor, [:or, [:plus, [:not, [:or, :ARG, 0]], 0], :ARG], :ARG]], :ARG, :ARG], :ARG]], :ARG]]]]], :ARG], :ARG]

  #prog = [:and, :ARG, :ARG]
  require 'pp'
  #pp prog
  pp bv.simple(prog)
  p [0, 1, 2, 4].map{|x| "%016x"%bv.eval(prog, x)}
end
