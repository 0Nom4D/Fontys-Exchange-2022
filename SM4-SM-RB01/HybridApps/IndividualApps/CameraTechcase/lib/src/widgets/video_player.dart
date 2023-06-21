import 'dart:io';
import 'package:flutter/material.dart';
import 'package:flutter/services.dart';

import 'package:photo_manager/photo_manager.dart';
import 'package:video_player/video_player.dart';

class CustomVideoPlayer extends StatefulWidget {
  const CustomVideoPlayer({required this.videoEntity, super.key});

  final AssetEntity videoEntity;

  @override
  State<CustomVideoPlayer> createState() => _CustomVideoPlayerState();
}

class _CustomVideoPlayerState extends State<CustomVideoPlayer> {
  VideoPlayerController? controller;

  @override
  void initState() {
    super.initState();
    _initVideoWithFile();
  }

  void _initVideoWithFile() {
    widget.videoEntity.file.then((File? file) {
      if (!mounted || file == null) {
        return;
      }
      controller = VideoPlayerController.file(file)
        ..initialize()
        ..addListener(() => setState(() {}));
      setState(() {});
    });
  }

  @override
  void dispose() {
    controller?.dispose();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) {
    if (controller?.value.isInitialized != true) {
      return const SizedBox.shrink();
    }

    final VideoPlayerController notNullController = controller!;
    return Stack(
      alignment: Alignment.bottomCenter,
      children: [
        AspectRatio(
          aspectRatio: notNullController.value.aspectRatio,
          child: VideoPlayer(notNullController),
        ),
        Row(
          children: [
            IconButton(
              onPressed: () {
                HapticFeedback.lightImpact();
                if (notNullController.value.isPlaying){
                  notNullController.pause();
                } else {
                  notNullController.play();
                }
                setState(() {});
              },
              icon: Icon(
                notNullController.value.isPlaying ? Icons.pause : Icons.play_arrow,
                color: Colors.white
              )
            ),
            IconButton(
              onPressed: () {
                notNullController.seekTo(const Duration(seconds: 0));
                setState(() {});
              },
              icon: const Icon(
                Icons.stop,
                color: Colors.white
              )
            )
          ],
        ),
        VideoProgressIndicator(
          notNullController,
          allowScrubbing: true,
          colors: const VideoProgressColors(
            backgroundColor: Colors.grey,
            playedColor: Colors.white,
            bufferedColor: Colors.black
          )
        ),
      ]
  );
  }
}