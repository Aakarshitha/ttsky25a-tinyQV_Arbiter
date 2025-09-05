
cd /home/runner
export PATH=/usr/bin:/bin:/tool/pandora64/bin:/apps/vcsmx/vcs/U-2023.03-SP2//bin:/usr/local/bin
export VCS_VERSION=U-2023.03-SP2
export VCS_PATH=/apps/vcsmx/vcs/U-2023.03-SP2//bin
export LM_LICENSE_FILE=27020@10.116.0.5
export VCS_HOME=/apps/vcsmx/vcs/U-2023.03-SP2/
export HOME=/home/runner
chmod +x run.bash; sed -i -e 's/\r//g' run.bash; ./run.bash  ; echo 'Creating result.zip...' && zip -r /tmp/tmp_zip_file_123play.zip . && mv /tmp/tmp_zip_file_123play.zip result.zip