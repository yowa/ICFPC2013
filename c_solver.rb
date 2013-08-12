require_relative 'bv'

def simple_candidates(problem)
  if problem.operators.size == 1
    op = problem.operators[0]

    progs = []
    if [:not, :shl1, :shr1, :shr4, :shr16].include?(op)
      [:x, 0, 1].each do |arg|
        prog = arg
        (problem.size-2).times do 
          prog = [op, prog]
        end
        progs << prog
      end
      return progs
    end
  end

  nil
end

def generate_candidates_c(problem)
  begin
    cands = []
    Open3.popen3("./list") do |fin, fout, ferr|
      fin.puts([problem.size, problem.operators.map{|x|":"+x.to_s}]*" ");
      fin.close

      fout.each do |l|
        prog = eval(l)
        cands << prog
      end
    end
    return cands
  rescue
    return nil
  end
end

def generate_candidates(problem)
  ops = problem.operators.dup
  size = problem.size
  
  if ops.include?(:tfold) 
    ops.delete(:tfold)
    cands = generate_candidates_sub(ops, size-4, [0,1,:x,:y,:z])
    return cands unless cands
    return cands.map{|prog| [:fold, :x, 0, :y, :z, prog]}

    return nil
  elsif ops.include?(:fold)
    return nil
  else
    return generate_candidates_sub(ops, size)
  end
end

def generate_candidates_sub(ops, size, ini=[0,1,:x])
  #return nil unless (ops & [:fold, :tfold]).empty?
  bv = BV.new

  mem = []
  mem[1] = ini
  2.upto(size-1) do |n|
    cur = []
    ops.each do |op|
      case op
      when :not, :shl1, :shr1, :shr4, :shr16
        mem[n-1].each do |x|
          #cur << bv.simple([op, x]) unless x.kind_of?(Numeric)
          cur << bv.simple([op, x])
        end
      when :and, :or, :xor, :plus
        1.upto(n-2) do |i|
          j = (n-1)-i
          break if j <= i
          #break if j < i
          mem[i].each do |x|
            mem[j].each do |y|
              cur << bv.simple([op, x, y])
            end
          end
        end

        if (n-1)%2 == 0
          k = (n-1)/2
          mem[k].size.times do |s|
            s.upto(mem[k].size-1) do |t|
            cur << bv.simple([op, mem[k][s], mem[k][t]])
            end
          end
        end
      when :if0
        1.upto(n-2) do |i|
          1.upto(n-2) do |j|
            k = n-(1+i+j)
            next if k <= 0
            #p [n, op, i, j, k]
            mem[i].each do |x|

              #simple
              if x == 0 && !mem[k].empty?
                mem[j].each do |y|
                  cur << y
                end
              elsif x.kind_of?(Numeric) && x > 0 && !mem[j].empty?
                mem[k].each do |z|
                  cur << z
                end
              else
                mem[j].each do |y|
                  mem[k].each do |z|
                    cur << bv.simple([op, x, y, z])
                  end
                end
              end
            end
          end
        end
      end
      #p [n, cur.size]
      return nil if cur.size > 300000
    end
    mem[n] = cur.uniq

    return nil if mem[n].size > 300000
  end
=begin
  puts "==="
  mem.each_with_index do |e, i|
    puts 
    puts "{{#{i}}}"
    e.each do |x|
      p x
    end if e && false
  end
=end
  mem.last
end

require 'open3'
class CSolver
  def initialize(problem, limit=nil)
    @fin, @fout = Open3.popen2("./list")
    @problem = problem
    @size = 0
    @fin.puts [limit||problem.size, problem.operators.map{|x|":"+x.to_s}]*" "
    @fin.flush
    sleep(0.01)
    @size = @fout.gets.to_i
  end
  attr_reader :size

  def narrow_down(arg, expected)
    @size = 0
    @fin.puts [arg, expected]*" "
    @fin.flush
    @size = @fout.gets.to_i
  end

  def get
    @fin.puts "get"
    @fin.flush
    progs = @fout.each_line.map{|str| eval(str)}

    progs
  end
end

=begin
bv = BV.new
#prog = [:fold, :x, 0, :y, :z, [:xor, [:not, :x], [:shr4, :y]]]
prog = [:fold, :x, 0, :y, :z, [:xor, [:shr4, [:not, 0]], :y]]
p "%016X"%bv.eval(prog, 0)
exit
=end

=begin
problem = Problem.new("12/[:if0, :plus, :shr1]")
#problem = Problem.new("5/[:plus, :shr1]")
require 'benchmark'
Benchmark.bm do |bm|
  bm.report{ generate_candidates(problem) }
  bm.report{ generate_candidates_c(problem) }
end
#cands = generate_candidates(problem)
cands = generate_candidates_c(problem)
p cands.size
bv = BV.new
cands.each{|x| p bv.dump(x) if bv.eval(x, 0x8CE3394791813618) == 0x0FFFFFFFFFFFFF73}
exit
=end

if __FILE__ == $0
  require 'net/http'
  require 'json'
  API_HOST = "icfpc2013.cloudapp.net"
  API_AUTH = "?auth=0097SHKnA2jVQ2NnopcbDJUvPnuMk6Q0V92OFpaIvpsH1H"
  $last_post = Time.now

  def post(path, body) 
    if Time.now < $last_post+5
      print "sleep.  \r"
      sleep($last_post+5 - Time.now)
      print "        \r"
    end
    $last_post = Time.now
    req = Net::HTTP::Post.new(path+API_AUTH)
    req.body = body
    Net::HTTP.start(API_HOST){|http| http.request(req)}
  end

  def http_guess(problem, prog)
    bv = BV.new
    h = { id: problem.id, program: bv.dump(prog)}
    p prog
    res = post("/guess", JSON.generate(h))

    begin
      return JSON.parse(res.body)
    rescue
      return res.body
    end
  end

  def http_eval(problem, args)
    #bv = BV.new
    h = { 
      id: problem.id, 
      #program: bv.dump(prog),
      arguments: args.map{|x| "0x%016X"%x}
    }
    #p prog

    res = post("/eval", JSON.generate(h))

    begin
      return JSON.parse(res.body)
    rescue
      puts "invalid responce? : "+res.body
      return nil
    end
  end

  def run
    $solved = []
    File.open("solved.txt", "r"){|f| f.each_line{|l| $solved << l.split[0]}}
    bv = BV.new

    enabled = false
    skip_here = "DxhBTNZyf7i5beJJ5e0wZA5H"

    problems = JSON.parse(ARGF.read).map{|x|Problem.new(x)}
    problems.each_with_index do |problem, lp|

      if problem.id == skip_here
        enabled = true
        next
      end
      next if !enabled

      next if $solved.include?(problem.id)
      next unless problem.active
      print "  ##{"%04d"%lp} #{problem.inspect[0,60]}     \n"
      #next if problem.operators.include?(:fold)
      #next if problem.operators.include?(:tfold)
      next if problem.operators.include?(:bonus)

      #next if problem.operators.size > 7

      #problem.operators.delete(:bonus)
      #next if problem.size > (problem.operators.include?(:tfold) ? 16 : 12)
      begin
        limit = [problem.size, 9+(problem.operators.include?(:tfold) ? 3 : 0)].min
        #limit = [problem.size, 10+(problem.operators.include?(:tfold) ? 3 : 0)].min
        #limit = [problem.size, 11+(problem.operators.include?(:tfold) ? 3 : 0)].min
        #limit = [problem.size, 12+(problem.operators.include?(:tfold) ? 3 : 0)].min
        #limit = [problem.size, 13+(problem.operators.include?(:tfold) ? 3 : 0)].min
        puts
        puts "> ##{"%04d"%lp} #{problem.inspect}"
        csolver = CSolver.new(problem, limit)
        #csolver = CSolver.new(problem)

        next if csolver.size == 0

        inputs = Array.new(10){rand(2**64)}+
          [0, 1, 0xff, (2**64-1), (2**64-2), (2**60-1), 0x0120deadbeef9876,
          0x0800000000000000]

        requested = true
        res = http_eval(problem, inputs)
        next unless res

        outputs = res["outputs"].map{|x|x.to_i(16)}
        pairs = inputs.zip(outputs)
        puts " cands: #{csolver.size}"
        pairs.each do |arg, expected| 
          sz = csolver.size
          csolver.narrow_down(arg, expected)
          #puts "  f(0x%016X) == 0x%016X : %d => %d "%[arg, expected, sz, csolver.size]
        end
        cands = csolver.get

        cands.each do |prog|
          next if pairs.any?{|x,y| bv.eval(prog, x) != y}
          puts "  #{prog.inspect}"
          puts "  #{bv.dump(prog)}"

          res = http_guess(problem, prog)
          p res
          if res
            if res['status'] == "win"
              $solved << problem.id
              File.open("solved.txt", "a") do |f|
                f.puts [problem.id, bv.dump(prog)]*"\t"
              end
              puts
              break
            elsif res['status'] == "mismatch"
              pairs << [res['values'][0].to_i(16), res['values'][1].to_i(16)]
            end
          end
        end

        if $solved.last != problem.id
          $stderr.puts
          $stderr.puts "****** MISS **********"
          $stderr.puts
          #system(%!ruby ~/Work/AquesTalk/say-roma.rb "mi'su"!)
          # akirameta
          #exit 
        end

      rescue Errno::EPIPE
        puts "rescue Errno::EPIPE"
        if requested && $solved.last != problem.id
          $stderr.puts "****** MISS **********"
          exit
        end
      end
    end
  end

  run
end

