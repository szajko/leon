package leon
package solvers
package bapaminmax

import java.io.FileWriter
import java.io.BufferedWriter

class CSVWriter(filename : String) {
  private val writer = new BufferedWriter(new FileWriter(filename))

  private val nl = System.getProperty("line.separator")

  def writeLine(str : String) : Unit = {
    writer.write(str)
    writer.write(nl)
    writer.flush()
  } 

  def close() : Unit = {
    writer.close()
  }
}
