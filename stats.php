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
      printf("%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n", 
          $this->name,
          $this->codeSize, $this->codeSizeNe,
          $this->fullSize, $this->fullSizeNe, 
          $this->invSize, $this->factsSize, $this->specSize, $this->verifSize);
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
   }

} 

$files = $argv;
unset($files[0]);
// var_dump($files);

printf("%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n",
   'dvpt', 'ml', 'real ml', 'coq', 'real coq', 'inv', 'facts', 'spec', 'verif');

$all = new dvpt('Total');

foreach ($files as $file)
{
   $dev = new dvpt;
   $dev->load($file);
   $dev->printInfos();
   $all->addFigures($dev);
}
$all->printInfos();

/*
$x = file_get_lines('demo/half.ml');
var_dump($x);
*/

?>