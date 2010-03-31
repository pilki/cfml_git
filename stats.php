<?php

function cleanup_line($line)
{
   return $line;
}

function file_get_lines($filename, $tags = array())
{
   $file = file_get_contents($filename);
   $lines = explode("\n", $file);
   $result = array();
   $bComment = false;
   foreach ($lines as $line)
   {
      $line = trim($line);
      if (in_array($line, $tags))
      {
         $result[] = $line;
         continue;
      }

      $newline = $line;
      if (strlen($line) >= 2 && substr($line,0,2) == '(*') 
      {
         $newline = '';
         $bComment = true;
      }
      if (strlen($line) >= 2 && substr($line,strlen($line)-2) == '*)') 
      {
         $newline = '';
         $bComment = false;
      }
      if ($bComment == true)
         $newline = '';

      $result[] = $newline;
   }
   return $result;
}

class dvpt 
{
   public $name, $vFile, $mlFile;
   public $codeSize = 0, $codeSizeNe = 0;
   public $fullSize = 0, $fullSizeNe = 0;
   public $invSize = 0, $specSize = 0, $factsSize = 0, $verifSize = 0;
   public $time = 0;

   public function __construct($name = '') 
   {
      $this->name = $name;
   }

   public function load($vFile)
   {
      $this->vFile = $vFile;
      $name = substr($vFile, 0, strlen($vFile)-strlen('_proof.v'));
      $this->mlFile = $name.".ml";
      $infos = pathinfo($name);
      $this->name = $infos['filename'] ;
      $this->codeInfos();
      $this->proofInfos();
   }

   private function codeInfos()
   { 
      $mlLines = file_get_lines($this->mlFile);
      $this->codeSize = 0;
      $this->codeSizeNe = 0;
      foreach ($mlLines as $line)
      {
         $this->codeSize++;
         if ($line != '')
            $this->codeSizeNe++;
      }
   }

   private function proofInfos() 
   {
      $proofTags = array(
      '(** instantiations *)',
      '(** invariant *)',
      '(** model *)',
      '(** automation *)',
      '(** verification *)',
      '(** useful facts *)');
      $tagIndex = array_flip($proofTags);
      $vLines = file_get_lines($this->vFile, $proofTags);
      $this->invSize = 0;
      $this->specSize = 0;
      $this->factsSize = 0;
      $this->verifSize = 0;
      $this->fullSize = 0;
      $tag = -1;
      $bSpec = false;
      $bProof = false;
      foreach ($vLines as $line)
      {
         $this->fullSize++;
         if (in_array($line, $proofTags))
         {
            $tag = $tagIndex[$line];
            continue;
         }
         if (empty($line))
            continue;
         $this->fullSizeNe++;

         if ($tag == $tagIndex['(** invariant *)'])
         {  
            $this->invSize++;
         }
         if ($tag == $tagIndex['(** useful facts *)'])
         {  
            $this->factsSize++;
         }
         else if ($tag == $tagIndex['(** verification *)'])
         {
            if ((strlen($line) >= 5 && substr($line,0,5) == 'Lemma') ||
                (strlen($line) >= 10 && substr($line,0,10) == 'Definition'))
               { $bSpec = true; $this->specSize++; } 
            else if (strlen($line) >= 6 && substr($line,0,6) == 'Proof.') 
               { $bSpec = false; $bProof = true; }
            else if (strlen($line) >= 4 && substr($line,0,6) == 'Qed.') 
               { $bProof = false; }
            else if ($bSpec)
               $this->specSize++;
            else if ($bProof)
               $this->verifSize++;
         }
      }
   }

   public function printInfos()
   {
      printf("%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%s\n", 
          $this->name,
          $this->codeSize, $this->codeSizeNe,
          $this->fullSize, $this->fullSizeNe, 
          $this->invSize, $this->factsSize, $this->specSize, $this->verifSize, $this->time);
   }

   public function measureTime()
   {
       $res = 0;
       $output = array();
       $cmd = "time -o time.txt -f %U coqc -I lib -I okasaki $this->vFile";
       fwrite(STDERR, "Timing $this->vFile \n$cmd \n"); 
       // echo "cmd = ".$cmd."\n";
       @exec($cmd, $output, $res);
       $this->time = trim(file_get_contents("time.txt"));
   }

   public function addFigures($dev)
   {
       $this->codeSize += $dev->codeSize;
       $this->codeSizeNe += $dev->codeSizeNe;
       $this->fullSize  += $dev->fullSize;
       $this->fullSizeNe += $dev->fullSizeNe; 
       $this->invSize += $dev->invSize;
       $this->factsSize += $dev->factsSize;
       $this->specSize += $dev->specSize;
       $this->verifSize += $dev->verifSize;
       $this->time += $dev->time;
   }

} 

$files = $argv;
unset($files[0]);
$times = false;
if ($files[1] == 'time')
{
   unset($files[1]);
   $times = true;
}
// var_dump($files);

$devs = array();
$all = new dvpt('Total');


foreach ($files as $file)
{
   $dev = new dvpt;
   $dev->load($file);
   if ($dev->name == "CatenableListImpl")
     $dev->name = "CatenableList";
   if ($dev->name == "BinaryRandomAccessList")
     $dev->name = "RandomAccessList";
   if ($dev->name == "BootstrappedQueue"
      || $dev->name == "AltBinaryRandomAccessList")
      continue;
   if ($times)
      $dev->measureTime();
   $all->addFigures($dev);
   $devs[] = $dev;
}
$devs[] = $all;



printf("%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n",
   'dvpt', 'ml', 'real_ml', 'coq', 'real_coq', 'inv', 'facts', 'spec', 'verif', 'time');
foreach ($devs as $dev)
   $dev->printInfos();
$all->printInfos();


$tex = '';
$tex .= sprintf("%s & %s & %s & %s & %s & %s & %s  %s \n",
'Development', 'Caml', 'Coq', 'inv', 'facts', 'spec', 'verif', '\\\\ \\hline');
foreach ($devs as $dev)
{
   if ($dev->name == "BootstrappedQueue"
      || $dev->name == "AltBinaryRandomAccessList")
      continue;
   $sep = '';
   if (in_array($dev->name, array('BankersDeque', 'BinomialHeap', 'RedBlackSet', 'RandomAccessList')))
      $sep = '\\hline';
     
   $tex .= sprintf("%s & %s & %s & %s & %s & %s & %s  %s \n",
         $dev->name, $dev->codeSizeNe, $dev->fullSizeNe, $dev->invSize, 
         $dev->factsSize, $dev->specSize, $dev->verifSize, '\\\\'.$sep);

}
file_put_contents('stats.tex', $tex);
echo $tex;

/*
$x = file_get_lines('demo/half.ml');
var_dump($x);
*/

?>
