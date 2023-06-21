import 'package:flutter/material.dart';

import 'package:photo_manager/photo_manager.dart';

import 'package:camera_techcase/src/widgets/video_player.dart';
import 'package:camera_techcase/src/widgets/top_app_bar.dart';

class VideoViewerScreen extends StatelessWidget {
  const VideoViewerScreen({required this.title, required this.videoEntity, super.key});

  final String title;
  final AssetEntity videoEntity;

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: CustomAppBar(title: title),
      body: CustomVideoPlayer(videoEntity: videoEntity),
    );
  }
}