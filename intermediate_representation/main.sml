structure Main =
struct
    fun compile filename = Semant.transProg (Parse.parse filename)
end
